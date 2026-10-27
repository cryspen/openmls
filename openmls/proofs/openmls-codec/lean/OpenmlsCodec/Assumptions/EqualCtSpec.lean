/- ASSUMED spec of the opaque `equal_ct` (`openmls/src/ciphersuite/mod.rs`), the constant-time
byte comparison of `Secret`'s (and `Mac`'s) `PartialEq`.

`equal_ct` is `opaque` in `hax.toml`: it logs (`log::error!` / `log::trace!`) when the lengths
differ, and the toolchain does not translate the `log` macros. Its extraction is the
signature-only stub of `Assumptions/FunsExternal.lean`.

Assumed: `equal_ct a b` returns (no panic) `true` exactly when the two slices have the same
contents (`false` when their lengths differ).

Justification: that is what the Rust body computes: it returns `false` when the lengths differ,
otherwise ORs the XORs of the byte pairs into `diff` and returns `diff == 0`; logging does not
change the result, and nothing in the body can panic. The assumption says nothing about timing
(the constant-time property is not modelled or verified).

Consistency: the structural comparison (`decide (a.val = b.val)`) is a model of the axiom.

Future work: prove it (needs a model of the `log` macros, or `equal_ct` without logging), then
remove this file. -/
import OpenmlsCodec.Extraction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

namespace openmls

/-- ASSUMED. `equal_ct` compares the contents of the two slices (see the file header). -/
axiom ciphersuite.equal_ct.spec (a b : Slice Std.U8) :
    ciphersuite.equal_ct a b = ok (decide (a.val = b.val))

end openmls
