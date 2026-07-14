# OpenMLS — formal verification

Verifying parts of [OpenMLS](https://github.com/openmls/openmls) (RFC 9420) by extracting
Rust to Lean with the [Hax](https://github.com/cryspen/hax) toolchain.

## Progress

**First target — ratchet-tree math (`treemath`).** *In progress.*

- Function contracts (pre/post-conditions) have been added directly to the Rust source
  (`openmls/src/binary_tree/array_representation/treemath.rs`) and travel through extraction.
- Panic-freedom + functional postconditions are being proved in
  [`aeneas-lean/`](aeneas-lean/). Most obligations are closed; a few proofs are still ongoing.

**Next target — OpenMLS validation checks.** The receiver-side message/commit validation
(the `ValSem*` checks) is the next unit slated for verification.
