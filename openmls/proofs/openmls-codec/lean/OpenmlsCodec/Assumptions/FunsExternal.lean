-- [openmls]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
module

public import Aeneas
public import CoreModels
public import OpenmlsCodec.Extraction.Types
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
open openmls

/- The `fmt` stubs below are the template's, with the spurious third component
(a backward function of `&mut Formatter`) dropped: the `fmt` field of CoreModels'
`Debug` is `… → RustM ((Result Unit fmt.Error) × Formatter)` (as in TlsCodec). -/

/-- [openmls::credentials::{impl core::fmt::Debug for openmls::credentials::CredentialType}::fmt]:
    Source: 'openmls/src/credentials/mod.rs', lines 80:22-80:27
    Visibility: public -/
axiom credentials.CredentialType.Insts.CoreFmtDebug.fmt
  :
  credentials.CredentialType → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [openmls::extensions::ratchet_tree_extension::{impl tls_codec::Size for openmls::extensions::ratchet_tree_extension::RatchetTreeExtension}::tls_serialized_len]:
    Source: 'openmls/src/extensions/ratchet_tree_extension.rs', lines 25:4-25:11
    Visibility: public -/
axiom
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.tls_serialized_len
  : extensions.ratchet_tree_extension.RatchetTreeExtension → RustM Std.Usize

/-- [openmls::messages::proposals::{impl core::fmt::Debug for openmls::messages::proposals::ProposalType}::fmt]:
    Source: 'openmls/src/messages/proposals.rs', lines 75:54-75:59
    Visibility: public -/
axiom messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt
  :
  messages.proposals.ProposalType → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [openmls::extensions::{impl core::fmt::Debug for openmls::extensions::ExtensionType}::fmt]:
    Source: 'openmls/src/extensions/mod.rs', lines 88:9-88:14
    Visibility: public -/
axiom extensions.ExtensionType.Insts.CoreFmtDebug.fmt
  :
  extensions.ExtensionType → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [openmls::extensions::ratchet_tree_extension::{impl tls_codec::Serialize for openmls::extensions::ratchet_tree_extension::RatchetTreeExtension}::tls_serialize]:
    Source: 'openmls/src/extensions/ratchet_tree_extension.rs', lines 22:4-22:16
    Visibility: public -/
axiom
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSerialize.tls_serialize
  {W : Type _} (coreiowriteWriteInst : core.io.write.Write W) :
  extensions.ratchet_tree_extension.RatchetTreeExtension → W → RustM
    ((core.result.Result Std.Usize tls_codec.Error) × W)

/-- [openmls::extensions::external_sender_extension::{impl core::fmt::Debug for openmls::extensions::external_sender_extension::ExternalSender}::fmt]:
    Source: 'openmls/src/extensions/external_sender_extension.rs', lines 19:4-19:9
    Visibility: public -/
axiom
  extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug.fmt
  :
  extensions.external_sender_extension.ExternalSender → core.fmt.Formatter
    → RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [openmls::extensions::ratchet_tree_extension::{impl tls_codec::Deserialize for openmls::extensions::ratchet_tree_extension::RatchetTreeExtension}::tls_deserialize]:
    Source: 'openmls/src/extensions/ratchet_tree_extension.rs', lines 23:4-23:18
    Visibility: public -/
axiom
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.tls_deserialize
  {R : Type _} (allocioreadReadInst : alloc.io.read.Read R) :
  R → RustM ((core.result.Result
    extensions.ratchet_tree_extension.RatchetTreeExtension tls_codec.Error) ×
    R)

/-- [openmls::extensions::{impl core::fmt::Debug for openmls::extensions::Extension}::fmt]:
    Source: 'openmls/src/extensions/mod.rs', lines 313:9-313:14
    Visibility: public -/
axiom extensions.Extension.Insts.CoreFmtDebug.fmt
  :
  extensions.Extension → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)


/-- [openmls::ciphersuite::equal_ct]:
    Source: 'openmls/src/ciphersuite/mod.rs', lines 54:0-68:1
    Opaque (`hax.toml`): its `log` macros are not translated. ASSUMED spec in
    `Assumptions/EqualCtSpec.lean`. -/
axiom ciphersuite.equal_ct : Slice Std.U8 → Slice Std.U8 → RustM Bool
