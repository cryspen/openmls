import OpenmlsCodec
import TlsCodec.Tools.AxiomGate

/-! Axiom whitelist gate: `lake env lean scripts/AxiomGate.lean` reports an error when a theorem
of a `OpenmlsCodec` module uses an axiom not listed in `scripts/axiom_whitelist.txt`. In an editor, the
language server caches the result: rebuild (or restart the server) after editing the whitelist. -/

#axiom_gate "OpenmlsCodec" "scripts/axiom_whitelist.txt"
