-- [openmls]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
module

public import Aeneas
public import CoreModels
public import TlsCodec.Extraction
public import TlsCodec.Assumptions.MissingCoreModels
public import TlsCodec.Assumptions.MissingThirdPartyModels
public import TraitsCodec.Extraction
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

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/-- [openmls::extensions::ratchet_tree_extension::RatchetTreeExtension]
    Source: 'openmls/src/extensions/ratchet_tree_extension.rs', lines 27:0-29:1
    Visibility: public -/
axiom extensions.ratchet_tree_extension.RatchetTreeExtension : Type


/-! The `ExtensionValidator` marker types, opaque in the scenario (`../../../../hax.toml`):
only used as type indices of the validator impls, whose bodies never touch a value. Lean
`opaque` constants (abstract, no axiom). -/

/-- [openmls::messages::group_info::GroupInfo] -/
opaque messages.group_info.GroupInfo : Type

/-- [openmls::group::group_context::GroupContext] -/
opaque group.group_context.GroupContext : Type

/-- [openmls::key_packages::KeyPackage] -/
opaque key_packages.KeyPackage : Type

/-- [openmls::treesync::node::leaf_node::LeafNode] -/
opaque treesync.node.leaf_node.LeafNode : Type
