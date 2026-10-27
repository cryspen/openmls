/- OpenmlsCodec: the tls_codec obligations of `openmls` (versions, ciphersuite, credentials,
extensions; scenario in `hax.toml`). Reading order: `Extraction/ProofObligations.lean`
(generated obligations, 195); `Assumptions/RatchetTreeSpecs.lean` (the ASSUMED contracts of the
opaque `RatchetTreeExtension`), `Assumptions/FmtAssumptions.lean` (ASSUMED: derived `Debug::fmt`
returns `Ok`), `Assumptions/EqualCtSpec.lean` (ASSUMED: the opaque `equal_ct` compares the bytes), `Assumptions/MissingStdModels.lean` (`ToString`, `LowerHex`, `HashSet` models) and
`Assumptions/TypesExternal.lean` / `FunsExternal.lean` (opaque types, `fmt` stubs); then `Verification/ProofObligations.lean` (the proofs, same statements) and
the hand-written `Extension` codec proofs it instantiates: `Verification/ExtensionStd.lean`
(deserializer), `ExtensionStdSer.lean` (serializer), `ExtensionsTryFrom.lean` (`ExtensionIn<T>`, `Extensions<T>`), `CanonicalSer.lean` (the
`u16`-coded serializers that reject non-canonical values), `RoundTrip.lean` (their round trip) and
`DecodersAgree.lean` (agreement of the hand-written `std` and byte-slice decoders).
Gates: `scripts/AxiomGate.lean`, `scripts/check_statements.py`; `Verification/AxiomCheck.lean`
prints the axioms of each obligation. -/
import OpenmlsCodec.Extraction
import OpenmlsCodec.Verification.ProofObligations
