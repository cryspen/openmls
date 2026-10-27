/- TraitsCodec: the tls_codec obligations of `openmls_traits` (scenario `traits-codec`, `hax.toml`).
Reading order: `Extraction/ProofObligations.lean` (generated obligations, 48), then
`Verification/ProofObligations.lean` (their proofs, same statements) and its helper
`Verification/StdHelpers.lean`. Assumed: nothing of its own (the hax-seeded `Assumptions/` files
are empty); TlsCodec's assumptions are inherited. Gates: `scripts/AxiomGate.lean`
(axioms vs `scripts/axiom_whitelist.txt`), `scripts/check_statements.py` (statements as generated);
`Verification/AxiomCheck.lean` prints the axioms of each obligation. -/
import TraitsCodec.Extraction
import TraitsCodec.Verification.ProofObligations
