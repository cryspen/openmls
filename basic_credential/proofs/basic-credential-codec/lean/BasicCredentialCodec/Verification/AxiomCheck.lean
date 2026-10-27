/- `#print axioms` of every obligation, for a manual cross-check of `scripts/AxiomGate.lean`
(not imported by the library; run it with `lake env lean <this file>`). -/
import BasicCredentialCodec.Verification.ProofObligations
open openmls_basic_credential
#print axioms SignatureKeyPair.Insts.Tls_codecSize.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecSerialize.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecDeserialize.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecDeserializeBytes.Lawful
#print axioms SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripStd.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecSpecIoNonEmptyStd.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecSpecIoDecodersAgree.Lawful
#print axioms SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripMixed.Lawful
