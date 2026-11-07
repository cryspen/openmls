/- Missing std models for the openmls extraction: `core` / `alloc` / `std` items that
upstream OpenMLS (2026-08, rebased onto `be248d4b1`) reaches and that neither CoreModels
(hax-lean v0.3.34) nor TlsCodec's `Assumptions/MissingCoreModels.lean` provide.
Crate-independent (imports only Aeneas, CoreModels and TlsCodec's core models), imported into
every generated file through `-extra-includes` (`../../../../hax.toml`). Candidates for moving to
TlsCodec's `MissingCoreModels.lean` / hax's core models.

Everything here is a `def` / `structure` (no axiom), with the deviations from std noted.
Reached by:
- `alloc::string::ToString`: the validator error of `ExtensionIn<T>::tls_deserialize`
  (`e.to_string()`, `T::Error: ToString`) and `"…".to_string()` in the canonicity checks of the
  `Serialize` impls (`ProtocolVersion`);
- `LowerHex` for `u16`: the `{value:#06x}` error messages of the canonicity checks
  (`CredentialType`, `ProposalType`, `ExtensionType` `Serialize`);
- `HashSet<ExtensionType>`: the duplicate check of `Extensions<T>::try_from(Vec<ExtensionIn<T>>)`. -/
module

public import Aeneas
public import CoreModels
public import TlsCodec.Assumptions.MissingCoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

namespace CoreModels

/-! ## `ToString` -/

/-- Trait declaration: [alloc::string::ToString] -/
structure alloc.string.ToString (Self : Type _) where
  to_string : Self → RustM alloc.string.String

/-- [alloc::string::{impl ToString for T}::to_string] (`T: Display`): std writes `self` into a
    fresh `String` through `Display::fmt` and panics ("a Display implementation returned an error
    unexpectedly") if it returns `Err`.
    DEVIATION(std): the text is not modelled (`Formatter` is `Unit`): the empty string, as
    `alloc.fmt.format`. -/
def alloc.string.ToString.Blanket.to_string
    {T : Type _} (DisplayInst : core.fmt.Display T) (x : T) : RustM alloc.string.String := do
  let (r, _) ← DisplayInst.fmt x ()
  match r with
  | .Ok () => ok ""
  | .Err _ => fail .panic

/-- [alloc::string::{impl ToString for T}] (`T: Display`). -/
@[reducible]
def alloc.string.ToString.Blanket {T : Type _} (DisplayInst : core.fmt.Display T) :
    alloc.string.ToString T := {
  to_string := alloc.string.ToString.Blanket.to_string DisplayInst
}

/-- [core::fmt::{impl Display for str}::fmt]: `f.pad(self)`; writing into a `String` sink (the
    only sink of `format!` / `to_string`) cannot fail. -/
def core.Str.Insts.CoreFmtDisplay.fmt (self : Str) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

/-- [core::fmt::{impl Display for str}] -/
@[reducible]
def core.Str.Insts.CoreFmtDisplay : core.fmt.Display Str := {
  fmt := core.Str.Insts.CoreFmtDisplay.fmt
}

/-! ## `LowerHex` -/

/-- Trait declaration: [core::fmt::LowerHex] -/
structure core.fmt.LowerHex (Self : Type _) where
  fmt : Self → core.fmt.Formatter → RustM ((core.result.Result Unit core.fmt.Error) ×
    core.fmt.Formatter)

/-- [core::fmt::num::{impl LowerHex for u16}::fmt]: as CoreModels' `Display` for `u16`
    (a `String` sink cannot fail). -/
def core.U16.Insts.CoreFmtLowerHex.fmt (self : Std.U16) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

/-- [core::fmt::num::{impl LowerHex for u16}] -/
@[reducible]
def core.U16.Insts.CoreFmtLowerHex : core.fmt.LowerHex Std.U16 := {
  fmt := core.U16.Insts.CoreFmtLowerHex.fmt
}

/-- [core::fmt::rt::{Argument}::new_lower_hex]: as `new_display` (same DEVIATION: `fmt` is
    called here, eagerly, and an `Err` panics as `format` would). -/
def core.fmt.rt.Argument.new_lower_hex
    {T : Type _} (LowerHexInst : core.fmt.LowerHex T) (x : T) :
    RustM core.fmt.rt.Argument := do
  let (r, _) ← LowerHexInst.fmt x ()
  match r with
  | .Ok () => ok ⟨.Placeholder ()⟩
  | .Err _ => fail .panic

/-! ## `HashSet` -/

/-- [std::hash::random::RandomState]: the random keys are not modelled. -/
@[reducible]
def std.hash.random.RandomState := Unit

/-- [std::hash::random::DefaultHasher]: not modelled. -/
@[reducible]
def std.hash.random.DefaultHasher := Unit

/-- Trait declaration: [core::hash::BuildHasher] (associated type `Hasher` lifted). -/
structure core.hash.BuildHasher (Self : Type _) (Self_Hasher : Type _) where
  build_hasher : Self → RustM Self_Hasher

/-- [std::hash::random::{impl BuildHasher for RandomState}] -/
@[reducible]
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher :
    core.hash.BuildHasher std.hash.random.RandomState std.hash.random.DefaultHasher := {
  build_hasher := fun _ => ok ()
}

/-- [std::collections::hash::set::HashSet]: modelled by the list of its elements (most recent
    first, no duplicates). The hasher state `S` and the allocator `A` are type indices only. -/
structure std.collections.hash.set.HashSet (T : Type _) (S : Type _) (A : Type _) where
  elems : List T

/-- [std::collections::hash::set::{HashSet<T, RandomState>}::with_capacity]: an empty set.
    DEVIATION(std): the capacity is not modelled (an allocation failure aborts in std). -/
def std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity (T : Type _)
    (_capacity : Std.Usize) :
    RustM (std.collections.hash.set.HashSet T std.hash.random.RandomState alloc.alloc.Global) :=
  ok ⟨[]⟩

open Classical in
/-- [std::collections::hash::set::{HashSet<T, S, A>}::insert] (`T: Eq + Hash`, `S: BuildHasher`):
    `true` and the extended set if no element equal to `value` was present, `false` and the set
    unchanged otherwise.
    DEVIATION(std): membership is Lean equality (classical), not the `Hash` / `Eq` impls. Equal
    to std when `Eq` decides `=` (`core.cmp.Eq.Lawful`) and `Hash` agrees with `Eq` (std's
    documented requirement; derived impls satisfy both). Growth (allocation failure aborts) is
    not modelled. -/
noncomputable def std.collections.hash.set.HashSet.insert
    {T S A Hasher : Type _} (EqInst : core.cmp.Eq T) (HashInst : core.hash.Hash T)
    (BuildHasherInst : core.hash.BuildHasher S Hasher)
    (self : std.collections.hash.set.HashSet T S A) (value : T) :
    RustM (Bool × std.collections.hash.set.HashSet T S A) :=
  if value ∈ self.elems then ok (false, self) else ok (true, ⟨value :: self.elems⟩)

end CoreModels

/-! ## `Lawful` structure of `ToString` (as TlsCodec's core trait `Lawful`s) -/

namespace CoreModels

/-- `to_string_spec`: `to_string` does not fail (no panic, no divergence); the result is
    unconstrained. A modelling choice (as `From.from`): the blanket impl panics only when the
    type's `Display::fmt` returns `Err` on a `String` sink, which std documents as a bug of that
    impl. A field is a proof obligation of each impl's `Lawful`, never an axiom. -/
structure alloc.string.ToString.Lawful (Self : Type _)
  (ToStringInst : alloc.string.ToString Self) : Prop where
  to_string_spec (x : Self) : ⦃ ⌜ True ⌝ ⦄ ToStringInst.to_string x ⦃ ⇓ _ => ⌜ True ⌝ ⦄

end CoreModels
