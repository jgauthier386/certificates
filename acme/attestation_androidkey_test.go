package acme

import (
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/sha256"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/asn1"
	"encoding/base64"
	"encoding/hex"
	"encoding/pem"
	"math/big"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/fxamacker/cbor/v2"
	"github.com/stretchr/testify/require"
	"go.step.sm/crypto/jose"
	"go.step.sm/crypto/keyutil"
	"go.step.sm/crypto/minica"
)

// ---------------------------------------------------------------------------
// Tiny DER builder for synthetic KeyDescription extensions (tests only).
// ---------------------------------------------------------------------------

func derWrap(class, tag int, constructed bool, content []byte) []byte {
	var out []byte
	b0 := byte(class<<6) | byte(tag)
	if constructed {
		b0 |= 0x20
	}
	if tag < 31 {
		out = append(out, b0)
	} else {
		out = append(out, byte(class<<6)|boolByte(constructed)|0x1F)
		var tb []byte
		for t := tag; t > 0; t >>= 7 {
			tb = append([]byte{byte(t & 0x7F)}, tb...)
		}
		for i := 0; i < len(tb)-1; i++ {
			tb[i] |= 0x80
		}
		out = append(out, tb...)
	}
	if len(content) < 128 {
		out = append(out, byte(len(content)))
	} else {
		n := []byte{}
		for l := len(content); l > 0; l >>= 8 {
			n = append([]byte{byte(l)}, n...)
		}
		out = append(out, 0x80|byte(len(n)))
		out = append(out, n...)
	}
	return append(out, content...)
}

func boolByte(b bool) byte {
	if b {
		return 0x20
	}
	return 0
}

func derConcat(parts ...[]byte) []byte {
	var out []byte
	for _, p := range parts {
		out = append(out, p...)
	}
	return out
}

func derSeq(parts ...[]byte) []byte { return derWrap(0, 16, true, derConcat(parts...)) }
func derSet(parts ...[]byte) []byte { return derWrap(0, 17, true, derConcat(parts...)) }
func derOctet(b []byte) []byte      { return derWrap(0, 4, false, b) }
func derExplicit(tag int, inner []byte) []byte {
	return derWrap(2, tag, true, inner)
}

func derInt(v int64) []byte {
	b, _ := asn1.Marshal(big.NewInt(v))
	return b
}

func derEnum(v int64) []byte {
	b, _ := asn1.Marshal(asn1.Enumerated(v))
	return b
}

func derBool(v bool) []byte {
	b, _ := asn1.Marshal(v)
	return b
}

type androidKeyDescriptionOpts struct {
	securityLevel int64
	locked        bool
	bootState     int64
	bootKey       []byte
	bootHash      []byte
	challenge     []byte
	osVersion     int64
	osPatch       int64
	vendorPatch   int64
	bootPatch     int64
	pkg           string
	sigDigest     []byte
}

func defaultAndroidKeyDescriptionOpts() androidKeyDescriptionOpts {
	bootKey, _ := hex.DecodeString("55a2d44103e56d5ec65496399c417987ba77730e6488fc60ba058d09fc3caee3")
	bootHash, _ := hex.DecodeString("3c60de31c35913eda1a68f8993d92f715703e9f5933978c22d6bb0f5dd68b283")
	sigDigest, _ := hex.DecodeString("b3d581f8f8f7f4731a3ddc91a8ddb4df5a514e8ec12f65b71e9cdcca18793f3d")
	return androidKeyDescriptionOpts{
		securityLevel: androidSecurityLevelStrongBox,
		locked:        true,
		bootState:     androidBootStateSelfSigned,
		bootKey:       bootKey,
		bootHash:      bootHash,
		challenge:     []byte("homelab-acme-da-phase0"),
		osVersion:     170000,
		osPatch:       202608,
		vendorPatch:   20260805,
		bootPatch:     20260805,
		pkg:           "house.gauthier.attestcapture",
		sigDigest:     sigDigest,
	}
}

func buildAndroidKeyDescriptionDER(o androidKeyDescriptionOpts) []byte {
	appID := derSeq(
		derSet(derSeq(derOctet([]byte(o.pkg)), derInt(1))),
		derSet(derOctet(o.sigDigest)),
	)
	software := derSeq(
		derExplicit(701, derInt(1786917406542)),
		derExplicit(709, derOctet(appID)),
	)
	hardware := derSeq(
		derExplicit(1, derSet(derInt(2))),
		derExplicit(2, derInt(3)),
		derExplicit(3, derInt(256)),
		derExplicit(5, derSet(derInt(4))),
		derExplicit(10, derInt(1)),
		derExplicit(702, derInt(0)),
		derExplicit(704, derSeq(
			derOctet(o.bootKey),
			derBool(o.locked),
			derEnum(o.bootState),
			derOctet(o.bootHash),
		)),
		derExplicit(705, derInt(o.osVersion)),
		derExplicit(706, derInt(o.osPatch)),
		derExplicit(718, derInt(o.vendorPatch)),
		derExplicit(719, derInt(o.bootPatch)),
	)
	return derSeq(
		derInt(300),
		derEnum(o.securityLevel),
		derInt(300),
		derEnum(o.securityLevel),
		derOctet(o.challenge),
		derOctet(nil),
		software,
		hardware,
	)
}

// ---------------------------------------------------------------------------
// Fixture-driven parser test (real GrapheneOS Pixel 10 Pro Fold capture).
// ---------------------------------------------------------------------------

func TestParseAndroidKeyDescription_fixture(t *testing.T) {
	pemBytes, err := os.ReadFile("testdata/android-key-leaf.pem")
	require.NoError(t, err)
	block, _ := pem.Decode(pemBytes)
	require.NotNil(t, block)
	leaf, err := x509.ParseCertificate(block.Bytes)
	require.NoError(t, err)

	var ext []byte
	for _, e := range leaf.Extensions {
		if e.Id.Equal(oidAndroidKeyAttestation) {
			ext = e.Value
		}
	}
	require.NotEmpty(t, ext, "fixture leaf must carry the keymaster extension")

	desc, err := parseAndroidKeyDescription(ext)
	require.NoError(t, err)

	require.Equal(t, int64(300), desc.AttestationVersion)
	require.Equal(t, int64(androidSecurityLevelStrongBox), desc.AttestationSecurityLevel)
	require.Equal(t, int64(300), desc.KeyMintVersion)
	require.Equal(t, int64(androidSecurityLevelStrongBox), desc.KeyMintSecurityLevel)
	require.Equal(t, []byte("homelab-acme-da-phase0"), desc.AttestationChallenge)

	require.True(t, desc.RootOfTrust.DeviceLocked)
	require.Equal(t, int64(androidBootStateSelfSigned), desc.RootOfTrust.VerifiedBootState)
	require.Equal(t,
		"55a2d44103e56d5ec65496399c417987ba77730e6488fc60ba058d09fc3caee3",
		hex.EncodeToString(desc.RootOfTrust.VerifiedBootKey))
	require.Equal(t,
		"3c60de31c35913eda1a68f8993d92f715703e9f5933978c22d6bb0f5dd68b283",
		hex.EncodeToString(desc.RootOfTrust.VerifiedBootHash))

	require.Equal(t, int64(170000), desc.OSVersion)
	require.Equal(t, int64(202608), desc.OSPatchLevel)
	require.Equal(t, int64(20260805), desc.VendorPatchLevel)
	require.Equal(t, int64(20260805), desc.BootPatchLevel)

	require.Equal(t, []string{"house.gauthier.attestcapture"}, desc.AttestationApplicationID.Packages)
	require.Len(t, desc.AttestationApplicationID.SignatureDigests, 1)
	require.Equal(t,
		"b3d581f8f8f7f4731a3ddc91a8ddb4df5a514e8ec12f65b71e9cdcca18793f3d",
		hex.EncodeToString(desc.AttestationApplicationID.SignatureDigests[0]))
}

func TestParseAndroidKeyDescription_syntheticRoundTrip(t *testing.T) {
	opts := defaultAndroidKeyDescriptionOpts()
	desc, err := parseAndroidKeyDescription(buildAndroidKeyDescriptionDER(opts))
	require.NoError(t, err)
	require.Equal(t, opts.securityLevel, desc.AttestationSecurityLevel)
	require.Equal(t, opts.locked, desc.RootOfTrust.DeviceLocked)
	require.Equal(t, opts.bootState, desc.RootOfTrust.VerifiedBootState)
	require.Equal(t, opts.bootKey, desc.RootOfTrust.VerifiedBootKey)
	require.Equal(t, opts.bootHash, desc.RootOfTrust.VerifiedBootHash)
	require.Equal(t, opts.osVersion, desc.OSVersion)
	require.Equal(t, opts.pkg, desc.AttestationApplicationID.Packages[0])
}

// ---------------------------------------------------------------------------
// End-to-end validation against a synthetic attestation CA.
// ---------------------------------------------------------------------------

func TestDoAndroidKeyAttestationFormat(t *testing.T) {
	ctx := context.Background()
	ca, err := minica.New()
	require.NoError(t, err)
	caRoot := pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: ca.Root.Raw})

	signer, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	require.NoError(t, err)

	makeLeaf := func(extDER []byte) *x509.Certificate {
		leaf, err := ca.Sign(&x509.Certificate{
			Subject:   pkix.Name{CommonName: "Android Keystore Key"},
			PublicKey: signer.Public(),
			ExtraExtensions: []pkix.Extension{
				{Id: oidAndroidKeyAttestation, Value: extDER},
			},
		})
		require.NoError(t, err)
		return leaf
	}

	jwk, err := jose.GenerateJWK("EC", "P-256", "ES256", "sig", "", 0)
	require.NoError(t, err)
	keyAuth, err := KeyAuthorization("token", jwk)
	require.NoError(t, err)
	keyAuthSum := sha256.Sum256([]byte(keyAuth))
	sig, err := signer.Sign(rand.Reader, keyAuthSum[:], crypto.SHA256)
	require.NoError(t, err)

	otherSigner, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	require.NoError(t, err)
	otherSig, err := otherSigner.Sign(rand.Reader, keyAuthSum[:], crypto.SHA256)
	require.NoError(t, err)

	rsaSigner, err := keyutil.GenerateSigner("RSA", "", 2048)
	require.NoError(t, err)
	rsaSig, err := rsaSigner.Sign(rand.Reader, keyAuthSum[:], crypto.SHA256)
	require.NoError(t, err)
	rsaLeaf, err := ca.Sign(&x509.Certificate{
		Subject:   pkix.Name{CommonName: "Android Keystore Key"},
		PublicKey: rsaSigner.Public(),
		ExtraExtensions: []pkix.Extension{
			{Id: oidAndroidKeyAttestation, Value: buildAndroidKeyDescriptionDER(defaultAndroidKeyDescriptionOpts())},
		},
	})
	require.NoError(t, err)

	goodLeaf := makeLeaf(buildAndroidKeyDescriptionDER(defaultAndroidKeyDescriptionOpts()))

	mutated := func(mutate func(*androidKeyDescriptionOpts)) []byte {
		o := defaultAndroidKeyDescriptionOpts()
		mutate(&o)
		return buildAndroidKeyDescriptionDER(o)
	}
	noExtLeaf, err := ca.Sign(&x509.Certificate{
		Subject:   pkix.Name{CommonName: "Android Keystore Key"},
		PublicKey: signer.Public(),
	})
	require.NoError(t, err)

	type args struct {
		provRoots []byte
		ch        *Challenge
		att       *attestationObject
	}
	tests := []struct {
		name       string
		args       args
		wantErr    bool
		wantErrSub string
	}{
		{"ok", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{goodLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, false, ""},
		{"ok/rsa", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{rsaLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-257),
				"sig": rsaSig,
			},
		}}, false, ""},
		{"fail/no-roots", args{nil, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{goodLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "no attestation roots"},
		{"fail/x5c-not-present", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format:       "android-key",
			AttStatement: map[string]interface{}{"alg": int64(-7), "sig": sig},
		}}, true, "x5c not present"},
		{"fail/x5c-wrong-root", args{mustOtherRootPEM(t), &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{goodLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "x5c is not valid"},
		{"fail/bad-sig", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{goodLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": otherSig,
			},
		}}, true, "failed to validate signature"},
		{"fail/wrong-alg", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{goodLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-257),
				"sig": sig,
			},
		}}, true, "unexpected alg"},
		{"fail/no-extension", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{noExtLeaf.Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "no keymaster attestation extension"},
		{"fail/software-level", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{makeLeaf(mutated(func(o *androidKeyDescriptionOpts) { o.securityLevel = 0 })).Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "security level is software"},
		{"fail/unlocked", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{makeLeaf(mutated(func(o *androidKeyDescriptionOpts) { o.locked = false })).Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "device is not locked"},
		{"fail/boot-unverified", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{makeLeaf(mutated(func(o *androidKeyDescriptionOpts) { o.bootState = 2 })).Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "not trustworthy"},
		{"fail/boot-failed", args{caRoot, &Challenge{Token: "token"}, &attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": []interface{}{makeLeaf(mutated(func(o *androidKeyDescriptionOpts) { o.bootState = 3 })).Raw, ca.Intermediate.Raw},
				"alg": int64(-7),
				"sig": sig,
			},
		}}, true, "not trustworthy"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := doAndroidKeyAttestationFormat(ctx, mustAttestationProvisioner(t, tt.args.provRoots), tt.args.ch, jwk, tt.args.att)
			if tt.wantErr {
				require.Error(t, err)
				require.Contains(t, err.Error(), tt.wantErrSub)
				return
			}
			require.NoError(t, err)
			expectedFP, err := keyutil.Fingerprint(mustParseCert(t, tt.args.att.AttStatement["x5c"].([]interface{})[0].([]byte)).PublicKey)
			require.NoError(t, err)
			require.Equal(t, expectedFP, got.Fingerprint)
			require.Equal(t, "StrongBox", got.SecurityLevel)
			require.True(t, got.DeviceLocked)
			require.Equal(t, "SelfSigned", got.VerifiedBootState)
			require.Equal(t, []string{"house.gauthier.attestcapture"}, got.Packages)
			require.Equal(t, int64(170000), got.OSVersion)
		})
	}
}

func mustParseCert(t *testing.T, der []byte) *x509.Certificate {
	t.Helper()
	cert, err := x509.ParseCertificate(der)
	require.NoError(t, err)
	return cert
}

func attestationFixtureTime(t *testing.T, x5c []interface{}) time.Time {
	t.Helper()
	currentTime := time.Time{}
	certificates := make([]*x509.Certificate, 0, len(x5c))
	for _, value := range x5c {
		der, ok := value.([]byte)
		require.True(t, ok, "x5c fixture entry must contain DER bytes")
		certificate := mustParseCert(t, der)
		certificates = append(certificates, certificate)
		if certificate.NotBefore.After(currentTime) {
			currentTime = certificate.NotBefore
		}
	}
	currentTime = currentTime.Add(time.Second)
	for _, certificate := range certificates {
		require.False(t, currentTime.After(certificate.NotAfter),
			"x5c fixture certificates have no overlapping validity window")
	}
	return currentTime
}

func mustOtherRootPEM(t *testing.T) []byte {
	t.Helper()
	other, err := minica.New()
	require.NoError(t, err)
	return pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: other.Root.Raw})
}

// TestDoAndroidKeyAttestationFormat_attObjFixture is the definitive
// end-to-end test: a real ACME attObj captured on the GrapheneOS device —
// real StrongBox chain, real extension, and a real signature over the key
// authorization of the fixed test account below. The fixture is produced by
// the lab-android-attest capture harness (homelab-auth repo); it skips when
// the capture has not been refreshed yet.
func TestDoAndroidKeyAttestationFormat_attObjFixture(t *testing.T) {
	b64, err := os.ReadFile("testdata/android-key-attobj.b64")
	if err != nil {
		t.Skipf("attObj fixture not present yet: %v", err)
	}
	rootPEM, err := os.ReadFile("testdata/android-key-google-root.pem")
	require.NoError(t, err)

	attObjDER, err := base64.RawURLEncoding.DecodeString(strings.TrimSpace(string(b64)))
	require.NoError(t, err)
	var att attestationObject
	require.NoError(t, cbor.Unmarshal(attObjDER, &att))
	require.Equal(t, "android-key", att.Format)

	// The fixed test account keypair the harness signs for.
	x, err := base64.RawURLEncoding.DecodeString("EpiFhkIGB46IbOkjpgn_LBJ0GVCK_GkKzQuopPkaiNU")
	require.NoError(t, err)
	y, err := base64.RawURLEncoding.DecodeString("fFsiCM653J5ckfEhVYNIZ9Jvb0KTyJA9io9foiJKzmg")
	require.NoError(t, err)
	jwk := &jose.JSONWebKey{Key: &ecdsa.PublicKey{
		Curve: elliptic.P256(),
		X:     new(big.Int).SetBytes(x),
		Y:     new(big.Int).SetBytes(y),
	}}

	// Guard fixture/JWK consistency: this must be exactly the message the
	// device signed.
	keyAuth, err := KeyAuthorization("homelab-test-token", jwk)
	require.NoError(t, err)
	require.Equal(t, "homelab-test-token.442P9fr8siV0ggQD4G7tiLYAWjvDvSka6tcXkN4IVOI", keyAuth)

	x5c := att.AttStatement["x5c"].([]interface{})
	leafDER := x5c[0].([]byte)
	leaf := mustParseCert(t, leafDER)
	got, err := doAndroidKeyAttestationFormatAt(context.Background(),
		mustAttestationProvisioner(t, rootPEM),
		&Challenge{Token: "homelab-test-token"},
		jwk,
		&att,
		attestationFixtureTime(t, x5c))
	require.NoError(t, err)

	expectedFP, err := keyutil.Fingerprint(leaf.PublicKey)
	require.NoError(t, err)
	require.Equal(t, expectedFP, got.Fingerprint)
	require.Equal(t, "StrongBox", got.SecurityLevel)
	require.True(t, got.DeviceLocked)
	require.Equal(t, "SelfSigned", got.VerifiedBootState)
}

// TestDoAndroidKeyAttestationFormat_googleChainFixture drives the real
// GrapheneOS attestation chain against Google's published attestation root.
// The fixture signature was made over a different message, so validation must
// reach (and only fail at) the signature check — proving chain verification
// and extension policy both pass on real device data.
func TestDoAndroidKeyAttestationFormat_googleChainFixture(t *testing.T) {
	rootPEM, err := os.ReadFile("testdata/android-key-google-root.pem")
	require.NoError(t, err)

	readDER := func(path string) []byte {
		b, err := os.ReadFile(path)
		require.NoError(t, err)
		block, _ := pem.Decode(b)
		require.NotNil(t, block)
		return block.Bytes
	}
	leafDER := readDER("testdata/android-key-leaf.pem")
	x5c := []interface{}{
		leafDER,
		readDER("testdata/android-key-chain-1.pem"),
		readDER("testdata/android-key-chain-2.pem"),
		readDER("testdata/android-key-chain-3.pem"),
	}

	jwk, err := jose.GenerateJWK("EC", "P-256", "ES256", "sig", "", 0)
	require.NoError(t, err)

	_, err = doAndroidKeyAttestationFormatAt(context.Background(),
		mustAttestationProvisioner(t, rootPEM),
		&Challenge{Token: "token"},
		jwk,
		&attestationObject{
			Format: "android-key",
			AttStatement: map[string]interface{}{
				"x5c": x5c,
				"alg": int64(-7),
				"sig": []byte{0x30, 0x00}, // structurally fine, cryptographically wrong
			},
		},
		attestationFixtureTime(t, x5c))
	require.Error(t, err)
	require.Contains(t, err.Error(), "failed to validate signature",
		"validation must reach the signature check on real fixture data, got: %v", err)
}
