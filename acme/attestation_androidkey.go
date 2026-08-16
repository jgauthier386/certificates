package acme

import (
	"context"
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/x509"
	"encoding/asn1"
	"fmt"
	"time"

	"go.step.sm/crypto/jose"
	"go.step.sm/crypto/keyutil"
)

// oidAndroidKeyAttestation identifies the Android key attestation extension
// (the KeyMint/Keymaster KeyDescription structure) in the leaf certificate of
// an android-key attestation statement's x5c chain.
//
//	https://source.android.com/docs/security/features/keystore/attestation
var oidAndroidKeyAttestation = asn1.ObjectIdentifier{1, 3, 6, 1, 4, 1, 11129, 2, 1, 17}

// COSE algorithm identifiers accepted for android-key attestations are the
// package's existing coseAlgES256 and coseAlgRS256 constants.

// Android KeyMint attestationSecurityLevel values.
const (
	androidSecurityLevelSoftware  = 0
	androidSecurityLevelTEE       = 1
	androidSecurityLevelStrongBox = 2
)

// Android rootOfTrust verifiedBootState values.
const (
	androidBootStateVerified   = 0
	androidBootStateSelfSigned = 1
	androidBootStateUnverified = 2
	androidBootStateFailed     = 3
)

// androidKeyAttestationData carries the verified facts of an android-key
// attestation, mirroring stepAttestationData for the existing formats.
type androidKeyAttestationData struct {
	// Fingerprint is the SHA-256 SPKI fingerprint of the attested key
	// (keyutil.Fingerprint). It is the device identifier of this format: it
	// must match the Order identifier and, at finalization, the CSR key.
	Fingerprint string
	// SecurityLevel is "TrustedEnvironment" or "StrongBox".
	SecurityLevel     string
	DeviceLocked      bool
	VerifiedBootState string
	VerifiedBootKey   []byte
	VerifiedBootHash  []byte
	// Packages and SignatureDigests form the attestationApplicationId.
	Packages         []string
	SignatureDigests [][]byte
	OSVersion        int64
	OSPatchLevel     int64
	VendorPatchLevel int64
	BootPatchLevel   int64
}

// doAndroidKeyAttestationFormat validates an ACME device-attest-01 attestation
// statement in the WebAuthn "android-key" format, as produced by Android's
// hardware-backed keystore (verified on GrapheneOS Pixels):
//
//   - the attStmt x5c chain must verify against the provisioner's configured
//     attestation roots (Google's key attestation roots);
//   - the keymaster extension must show a hardware security level
//     (TrustedEnvironment or StrongBox), a locked device, and a verified boot
//     state (Verified or SelfSigned — GrapheneOS uses SelfSigned with its own
//     AVB key);
//   - the attStmt sig must be a valid signature over
//     SHA-256(keyAuthorization) by the attested key, binding the attestation
//     to this ACME account and challenge token.
func doAndroidKeyAttestationFormat(_ context.Context, prov Provisioner, ch *Challenge, jwk *jose.JSONWebKey, att *attestationObject) (*androidKeyAttestationData, error) {
	// Unlike the step format (built-in Yubico roots), android-key has no
	// embedded default: the operator must configure Google's key attestation
	// roots explicitly on the provisioner.
	roots, ok := prov.GetAttestationRoots()
	if !ok {
		return nil, NewErrorISE("no attestation roots configured for the android-key format")
	}

	// Extract and verify the x5c certificate chain.
	x5c, ok := att.AttStatement["x5c"].([]interface{})
	if !ok {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "x5c not present")
	}
	if len(x5c) == 0 {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "x5c is empty")
	}
	der, ok := x5c[0].([]byte)
	if !ok {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "x5c is malformed")
	}
	leaf, err := x509.ParseCertificate(der)
	if err != nil {
		return nil, WrapDetailedError(ErrorBadAttestationStatementType, err, "x5c is malformed")
	}
	intermediates := x509.NewCertPool()
	for _, v := range x5c[1:] {
		der, ok = v.([]byte)
		if !ok {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "x5c is malformed")
		}
		cert, err := x509.ParseCertificate(der)
		if err != nil {
			return nil, WrapDetailedError(ErrorBadAttestationStatementType, err, "x5c is malformed")
		}
		intermediates.AddCert(cert)
	}
	if _, err := leaf.Verify(x509.VerifyOptions{
		Intermediates: intermediates,
		Roots:         roots,
		CurrentTime:   time.Now().Truncate(time.Second),
		KeyUsages:     []x509.ExtKeyUsage{x509.ExtKeyUsageAny},
	}); err != nil {
		return nil, WrapDetailedError(ErrorBadAttestationStatementType, err, "x5c is not valid")
	}

	// Parse and check the keymaster attestation extension before the crypto
	// check: structural and policy failures are the more useful signal.
	var ext []byte
	for _, e := range leaf.Extensions {
		if e.Id.Equal(oidAndroidKeyAttestation) {
			ext = e.Value
			break
		}
	}
	if len(ext) == 0 {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "leaf certificate carries no keymaster attestation extension")
	}
	desc, err := parseAndroidKeyDescription(ext)
	if err != nil {
		return nil, WrapDetailedError(ErrorBadAttestationStatementType, err, "keymaster attestation extension is malformed")
	}
	if desc.AttestationSecurityLevel == androidSecurityLevelSoftware {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "attestation security level is software")
	}
	if !desc.RootOfTrust.DeviceLocked {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "device is not locked")
	}
	if desc.RootOfTrust.VerifiedBootState > androidBootStateSelfSigned {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "verified boot state %d is not trustworthy", desc.RootOfTrust.VerifiedBootState)
	}

	// Verify the proof-of-possession signature over SHA-256 of the key
	// authorization, binding the attestation to this account and token.
	sig, ok := att.AttStatement["sig"].([]byte)
	if !ok {
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "sig not present")
	}
	alg, _ := att.AttStatement["alg"].(int64)
	keyAuth, err := KeyAuthorization(ch.Token, jwk)
	if err != nil {
		return nil, err
	}
	sum := sha256.Sum256([]byte(keyAuth))
	switch pub := leaf.PublicKey.(type) {
	case *ecdsa.PublicKey:
		if pub.Curve != elliptic.P256() {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "unsupported elliptic curve %s", pub.Curve)
		}
		if alg != 0 && coseAlgorithmIdentifier(alg) != coseAlgES256 {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "unexpected alg %d for an ECDSA P-256 key", alg)
		}
		if !ecdsa.VerifyASN1(pub, sum[:], sig) {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "failed to validate signature")
		}
	case *rsa.PublicKey:
		if alg != 0 && coseAlgorithmIdentifier(alg) != coseAlgRS256 {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "unexpected alg %d for an RSA key", alg)
		}
		if err := rsa.VerifyPKCS1v15(pub, crypto.SHA256, sum[:], sig); err != nil {
			return nil, NewDetailedError(ErrorBadAttestationStatementType, "failed to validate signature")
		}
	default:
		return nil, NewDetailedError(ErrorBadAttestationStatementType, "unsupported public key type %T", pub)
	}

	fingerprint, err := keyutil.Fingerprint(leaf.PublicKey)
	if err != nil {
		return nil, WrapErrorISE(err, "error computing attested key fingerprint")
	}

	return &androidKeyAttestationData{
		Fingerprint:       fingerprint,
		SecurityLevel:     androidSecurityLevelName(desc.AttestationSecurityLevel),
		DeviceLocked:      desc.RootOfTrust.DeviceLocked,
		VerifiedBootState: androidBootStateName(desc.RootOfTrust.VerifiedBootState),
		VerifiedBootKey:   desc.RootOfTrust.VerifiedBootKey,
		VerifiedBootHash:  desc.RootOfTrust.VerifiedBootHash,
		Packages:          desc.AttestationApplicationID.Packages,
		SignatureDigests:  desc.AttestationApplicationID.SignatureDigests,
		OSVersion:         desc.OSVersion,
		OSPatchLevel:      desc.OSPatchLevel,
		VendorPatchLevel:  desc.VendorPatchLevel,
		BootPatchLevel:    desc.BootPatchLevel,
	}, nil
}

func androidSecurityLevelName(level int64) string {
	switch level {
	case androidSecurityLevelSoftware:
		return "Software"
	case androidSecurityLevelTEE:
		return "TrustedEnvironment"
	case androidSecurityLevelStrongBox:
		return "StrongBox"
	default:
		return fmt.Sprintf("Unknown(%d)", level)
	}
}

func androidBootStateName(state int64) string {
	switch state {
	case androidBootStateVerified:
		return "Verified"
	case androidBootStateSelfSigned:
		return "SelfSigned"
	case androidBootStateUnverified:
		return "Unverified"
	case androidBootStateFailed:
		return "Failed"
	default:
		return fmt.Sprintf("Unknown(%d)", state)
	}
}

// ---------------------------------------------------------------------------
// KeyMint KeyDescription (attestation extension) parsing.
// https://source.android.com/docs/security/features/keystore/attestation
//
// KeyDescription ::= SEQUENCE {
//   attestationVersion       INTEGER,
//   attestationSecurityLevel ENUMERATED,
//   keyMintVersion           INTEGER,
//   keyMintSecurityLevel     ENUMERATED,
//   attestationChallenge     OCTET_STRING,
//   uniqueId                 OCTET_STRING,
//   softwareEnforced         AuthorizationList,
//   hardwareEnforced         AuthorizationList }
//
// AuthorizationList ::= SEQUENCE { tag [N] EXPLICIT value, ... }
// ---------------------------------------------------------------------------

type androidRootOfTrust struct {
	VerifiedBootKey   []byte
	DeviceLocked      bool
	VerifiedBootState int64
	VerifiedBootHash  []byte
}

type androidApplicationID struct {
	Packages         []string
	SignatureDigests [][]byte
}

type androidKeyDescription struct {
	AttestationVersion       int64
	AttestationSecurityLevel int64
	KeyMintVersion           int64
	KeyMintSecurityLevel     int64
	AttestationChallenge     []byte
	RootOfTrust              androidRootOfTrust
	AttestationApplicationID androidApplicationID
	OSVersion                int64
	OSPatchLevel             int64
	VendorPatchLevel         int64
	BootPatchLevel           int64
}

// unmarshalRawValue unmarshals exactly one TLV from data into an
// asn1.RawValue and returns the remaining bytes.
func unmarshalRawValue(data []byte) (asn1.RawValue, []byte, error) {
	var raw asn1.RawValue
	rest, err := asn1.Unmarshal(data, &raw)
	if err != nil {
		return raw, nil, err
	}
	return raw, rest, nil
}

// rawChildren returns the raw TLVs contained in a constructed value
// (SEQUENCE or SET content octets).
func rawChildren(content []byte) ([]asn1.RawValue, error) {
	var out []asn1.RawValue
	for len(content) > 0 {
		raw, rest, err := unmarshalRawValue(content)
		if err != nil {
			return nil, err
		}
		out = append(out, raw)
		content = rest
	}
	return out, nil
}

// parseAndroidKeyDescription parses the KeyDescription structure. Go's
// encoding/asn1 cannot express the context-specific EXPLICIT tags used by the
// AuthorizationList, so the structure is walked with asn1.RawValue.
func parseAndroidKeyDescription(der []byte) (*androidKeyDescription, error) {
	top, rest, err := unmarshalRawValue(der)
	if err != nil {
		return nil, err
	}
	if len(rest) != 0 {
		return nil, fmt.Errorf("trailing data after KeyDescription")
	}
	fields, err := rawChildren(top.Bytes)
	if err != nil {
		return nil, err
	}
	if len(fields) < 8 {
		return nil, fmt.Errorf("KeyDescription has %d fields, want at least 8", len(fields))
	}
	desc := &androidKeyDescription{}
	if desc.AttestationVersion, err = rawInt(fields[0]); err != nil {
		return nil, fmt.Errorf("attestationVersion: %w", err)
	}
	if desc.AttestationSecurityLevel, err = rawInt(fields[1]); err != nil {
		return nil, fmt.Errorf("attestationSecurityLevel: %w", err)
	}
	if desc.KeyMintVersion, err = rawInt(fields[2]); err != nil {
		return nil, fmt.Errorf("keyMintVersion: %w", err)
	}
	if desc.KeyMintSecurityLevel, err = rawInt(fields[3]); err != nil {
		return nil, fmt.Errorf("keyMintSecurityLevel: %w", err)
	}
	desc.AttestationChallenge = fields[4].Bytes
	if err := parseAndroidAuthorizationList(fields[6].Bytes, desc, false); err != nil {
		return nil, fmt.Errorf("softwareEnforced: %w", err)
	}
	if err := parseAndroidAuthorizationList(fields[7].Bytes, desc, true); err != nil {
		return nil, fmt.Errorf("hardwareEnforced: %w", err)
	}
	return desc, nil
}

// rawInt decodes a DER INTEGER or ENUMERATED (both are two's-complement
// big-endian integers; encoding/asn1 only maps INTEGER to big.Int).
func rawInt(raw asn1.RawValue) (int64, error) {
	if raw.Class != 0 || (raw.Tag != 2 && raw.Tag != 10) {
		return 0, fmt.Errorf("expected INTEGER or ENUMERATED, got class %d tag %d", raw.Class, raw.Tag)
	}
	b := raw.Bytes
	if len(b) == 0 || len(b) > 8 {
		return 0, fmt.Errorf("invalid integer length %d", len(b))
	}
	var n int64
	if b[0]&0x80 != 0 {
		n = -1
	}
	for _, c := range b {
		n = n<<8 | int64(c)
	}
	return n, nil
}

// parseAndroidAuthorizationList walks a KeyMint AuthorizationList, filling in
// the fields of desc that this format records or enforces. The hardware
// Enforced list carries rootOfTrust and patch levels; the software list
// carries the attestationApplicationId.
func parseAndroidAuthorizationList(content []byte, desc *androidKeyDescription, hardware bool) error {
	entries, err := rawChildren(content)
	if err != nil {
		return err
	}
	for _, e := range entries {
		if e.Class != 2 { // context-specific
			continue
		}
		switch e.Tag {
		case 704: // rootOfTrust
			rot, err := parseAndroidRootOfTrust(e.Bytes)
			if err != nil {
				return err
			}
			desc.RootOfTrust = rot
		case 705: // osVersion
			if desc.OSVersion, err = rawExplicitInt(e.Bytes); err != nil {
				return err
			}
		case 706: // osPatchLevel
			if desc.OSPatchLevel, err = rawExplicitInt(e.Bytes); err != nil {
				return err
			}
		case 709: // attestationApplicationId
			appID, err := parseAndroidApplicationID(e.Bytes)
			if err != nil {
				return err
			}
			desc.AttestationApplicationID = appID
		case 718: // vendorPatchLevel
			if desc.VendorPatchLevel, err = rawExplicitInt(e.Bytes); err != nil {
				return err
			}
		case 719: // bootPatchLevel
			if desc.BootPatchLevel, err = rawExplicitInt(e.Bytes); err != nil {
				return err
			}
		}
	}
	return nil
}

// rawExplicitInt decodes a context-specific EXPLICIT wrapped INTEGER.
func rawExplicitInt(content []byte) (int64, error) {
	inner, _, err := unmarshalRawValue(content)
	if err != nil {
		return 0, err
	}
	return rawInt(inner)
}

// parseAndroidRootOfTrust parses
//
//	RootOfTrust ::= SEQUENCE { verifiedBootKey OCTET_STRING,
//	  deviceLocked BOOLEAN, verifiedBootState ENUMERATED,
//	  verifiedBootHash OCTET_STRING }
func parseAndroidRootOfTrust(content []byte) (androidRootOfTrust, error) {
	var rot androidRootOfTrust
	seq, _, err := unmarshalRawValue(content)
	if err != nil {
		return rot, err
	}
	fields, err := rawChildren(seq.Bytes)
	if err != nil {
		return rot, err
	}
	if len(fields) < 4 {
		return rot, fmt.Errorf("rootOfTrust has %d fields, want at least 4", len(fields))
	}
	rot.VerifiedBootKey = fields[0].Bytes
	var locked bool
	if _, err := asn1.Unmarshal(fields[1].FullBytes, &locked); err != nil {
		return rot, fmt.Errorf("deviceLocked: %w", err)
	}
	rot.DeviceLocked = locked
	if rot.VerifiedBootState, err = rawInt(fields[2]); err != nil {
		return rot, fmt.Errorf("verifiedBootState: %w", err)
	}
	rot.VerifiedBootHash = fields[3].Bytes
	return rot, nil
}

// parseAndroidApplicationID parses the OCTET STRING content of
// attestationApplicationId, itself DER:
//
//	AttestationApplicationId ::= SEQUENCE {
//	  package_infos     SET OF AttestationPackageInfo, -- { name, version }
//	  signature_digests SET OF OCTET_STRING }
func parseAndroidApplicationID(content []byte) (androidApplicationID, error) {
	var appID androidApplicationID
	octets, _, err := unmarshalRawValue(content)
	if err != nil {
		return appID, err
	}
	seq, _, err := unmarshalRawValue(octets.Bytes)
	if err != nil {
		return appID, err
	}
	sets, err := rawChildren(seq.Bytes)
	if err != nil {
		return appID, err
	}
	if len(sets) >= 1 {
		pkgs, err := rawChildren(sets[0].Bytes)
		if err != nil {
			return appID, err
		}
		for _, pkg := range pkgs {
			fields, err := rawChildren(pkg.Bytes)
			if err != nil || len(fields) < 2 {
				continue
			}
			appID.Packages = append(appID.Packages, string(fields[0].Bytes))
		}
	}
	if len(sets) >= 2 {
		digests, err := rawChildren(sets[1].Bytes)
		if err != nil {
			return appID, err
		}
		for _, d := range digests {
			appID.SignatureDigests = append(appID.SignatureDigests, d.Bytes)
		}
	}
	return appID, nil
}
