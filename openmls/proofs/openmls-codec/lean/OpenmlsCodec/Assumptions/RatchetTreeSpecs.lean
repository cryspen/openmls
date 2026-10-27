/- ASSUMED contracts of the opaque `RatchetTreeExtension` codec.

`RatchetTreeExtension` is `opaque` in `hax.toml`: its `Size` / `Serialize` / `Deserialize` impls
are mutually recursive with `Extension`'s and `Extensions<T>`'s through
`RatchetTreeIn → NodeIn → LeafNodeIn → LeafNodePayload → Extensions<_> → Extension`, and aeneas
rejects such groups ("Mixed declaration groups … are not supported yet", checked 2026-10-26 by
removing the `opaque` entries). Their extractions are bare axioms
(`Assumptions/FunsExternal.lean`) with no behaviour, so nothing can be proved about them.

What is assumed here is exactly the generated per-impl obligation (the trait-level contracts of
tls_codec, statements in `Extraction/ProofObligations.lean`) for two of those impls:

* `Size`: `tls_serialized_len` returns (no panic, no divergence). The trait-level post is `true`.
* `Deserialize`: (i) `tls_deserialize` on a lawful reader returns; on `Ok v` the reader's view
  lost exactly `tls_serialized_len v` bytes from its front (and is a suffix of the old view);
  (ii) `tls_deserialize_exact` (the provided default body) meets its post: `Ok v` only when the
  slice is exactly `tls_serialized_len v` bytes.

Justification: the Rust impls are `#[derive(TlsSize, TlsDeserialize)]` on a newtype over
`RatchetTreeIn` (= `Vec<Option<NodeIn>>`), i.e. the same derive / `Vec` / `Option` code whose
contracts are proved for every non-recursive instance in this project and in TlsCodec; the
recursion is structural over a finite tree (terminates). The `Size` sums use `len_add`
(saturating, so total).

Consistency: the impls are opaque axioms, so the assumptions only constrain them; a model exists
(`tls_serialized_len _ = ok 0`, `tls_deserialize` always `Err`: every post holds on `Err`).

* `Serialize` (beyond the generated obligations; the owner's answer covers "its impls"): the
  `Serialize` impl has no generated obligation and no instance record in this scenario (only
  its `tls_serialize` function is extracted, called by `Extension`'s serializer), so
  `serializeInst` below packs it with the `Size` impl and the default `tls_serialize_detached`
  (as the derive does), and its `Serialize.Lawful` is ASSUMED: it is what the proof of
  `Extension`'s `Serialize.Lawful` needs for the `RatchetTree` variant.

Consistency of the `Serialize` one: in the same model, `tls_serialize` always returns `Err`
(leaving the writer unchanged); then `spec.io.encode` is `Err` too and every post holds.

Remove this file when treesync is extracted with its recursion (needs aeneas support for
mutually recursive trait impls). -/
import OpenmlsCodec.Extraction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option linter.dupNamespace false

noncomputable section

namespace openmls

/-- ASSUMED: `RatchetTreeExtension::tls_serialized_len` is total (see the file header). -/
axiom extensions.ratchet_tree_extension.RatchetTreeExtension.size_lawful_assumed :
  tls_codec.Size.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize

/-- ASSUMED: `RatchetTreeExtension`'s `std` deserializer meets tls_codec's trait-level
contracts (see the file header). -/
axiom extensions.ratchet_tree_extension.RatchetTreeExtension.deserialize_lawful_assumed :
  tls_codec.Deserialize.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize

/-- MODEL (not an axiom): the `Serialize` instance of `RatchetTreeExtension`, as the derive
builds it (its extracted `tls_serialize`, the `Size` impl, the default `tls_serialize_detached`). -/
@[reducible]
impl_def extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst : tls_codec.Serialize
  extensions.ratchet_tree_extension.RatchetTreeExtension := {
  SizeInst := extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize
  tls_serialize := fun {W : Type} (coreiowriteWriteInst : core.io.write.Write W) =>
    extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSerialize.tls_serialize
    coreiowriteWriteInst
  tls_serialize_detached := tls_codec.Serialize.tls_serialize_detached.default
    extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst
}

/-- ASSUMED: `RatchetTreeExtension`'s `std` serializer meets tls_codec's trait-level contracts
(see the file header; needed by `Extension`'s `Serialize.Lawful`). -/
axiom extensions.ratchet_tree_extension.RatchetTreeExtension.serialize_lawful_assumed :
  tls_codec.Serialize.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
  extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst

end openmls
