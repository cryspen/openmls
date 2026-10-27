/- BasicCredentialCodec: the tls_codec obligations of `openmls_basic_credential` (scenario in
`hax.toml`). Reading order: `Extraction/ProofObligations.lean` (generated
obligations, 9), then `Verification/ProofObligations.lean` (their proofs, same statements).
Assumed: nothing of its own (the hax-seeded `Assumptions/` files are empty); TlsCodec's assumptions are inherited. Gates: `scripts/AxiomGate.lean`,
`scripts/check_statements.py`; `Verification/AxiomCheck.lean` prints the axioms of each obligation. -/
import BasicCredentialCodec.Extraction
import BasicCredentialCodec.Verification.ProofObligations
