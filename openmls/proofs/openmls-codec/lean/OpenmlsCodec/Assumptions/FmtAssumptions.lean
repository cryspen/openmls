/- ASSUMED specs of signature-only `Debug::fmt` stubs (`Assumptions/FunsExternal.lean`), reached
since upstream OpenMLS (2026-08) rejects non-canonical `u16` codes in the `Serialize` impls of
`CredentialType`, `ProposalType` and `ExtensionType` with
`Error::EncodingError(format!("{self:?} is encoded as {value:#06x}, which decodes as …"))`:
`format!` panics if `Debug::fmt` returns `Err`, so the serializers' panic freedom needs `fmt` to
return `Ok`. Imported by the proofs only (not by the generated files). Every proof using one shows
it in `#print axioms` (`scripts/axiom_whitelist.txt`).

Criterion (TlsCodec `Assumptions/FmtAssumptions.lean`): an ASSUMED
"`fmt` returns `Ok`" is honest only for an impl whose output is fixed code writing to the
formatter, since a `fmt::Error` can then come only from the sink, and the only formatter in the
model is `format!`'s (sink: a `String`, which never fails; the `Formatter` is `Unit`, so the
axiom cannot name it). The three impls below are `#[derive(Debug)]` on enums whose fields are
`u16` (`Grease(u16)`, `Other(u16)` / `Custom(u16)`, `Unknown(u16)`) or none: the derive writes the
variant name and, for a field, `u16`'s `Debug` via `debug_tuple_field1_finish`; no user code. -/
import Aeneas
import Hax
import OpenmlsCodec.Extraction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
open Std.Do

namespace openmls

/-- ASSUMED. The derived `Debug::fmt` of `CredentialType` returns `Ok` (see the file header). -/
@[spec]
axiom credentials.CredentialType.Insts.CoreFmtDebug.fmt.ok_spec
    (x : credentials.CredentialType) (f : core.fmt.Formatter) :
    ⦃ ⌜ True ⌝ ⦄ credentials.CredentialType.Insts.CoreFmtDebug.fmt x f
    ⦃ ⇓ p => ⌜ p.1 = .Ok () ⌝ ⦄

/-- ASSUMED. The derived `Debug::fmt` of `ProposalType` returns `Ok` (see the file header). -/
@[spec]
axiom messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt.ok_spec
    (x : messages.proposals.ProposalType) (f : core.fmt.Formatter) :
    ⦃ ⌜ True ⌝ ⦄ messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt x f
    ⦃ ⇓ p => ⌜ p.1 = .Ok () ⌝ ⦄

/-- ASSUMED. The derived `Debug::fmt` of `ExtensionType` returns `Ok` (see the file header). -/
@[spec]
axiom extensions.ExtensionType.Insts.CoreFmtDebug.fmt.ok_spec
    (x : extensions.ExtensionType) (f : core.fmt.Formatter) :
    ⦃ ⌜ True ⌝ ⦄ extensions.ExtensionType.Insts.CoreFmtDebug.fmt x f
    ⦃ ⇓ p => ⌜ p.1 = .Ok () ⌝ ⦄

end openmls
