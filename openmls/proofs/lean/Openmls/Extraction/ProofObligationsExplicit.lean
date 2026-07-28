-- Derived by hand from `Openmls.Extraction.ProofObligations` (AENEAS-generated).
-- [openmls]: proof obligations — EXPLICIT form.
-- Same 19 obligations as `ProofObligations.lean`, but each theorem's statement has its
-- `<fn>.spec <args>` reference inlined to the explicit Hoare-triple it unfolds to (the body of
-- the corresponding `<fn>.spec` in `Specs.lean`): the precondition `(<fn>.pre <args>).holds →`
-- (present for all 19 obligations in this census) followed by
-- `⦃⌜True⌝⦄ <fn> <args> ⦃⇓ res => …⦄`. The `.pre`/`.post` components are left as named
-- references (they are themselves defined explicitly in `Specs.lean`, now in `Result Bool`
-- bool-encoded form, so `.holds` applies unchanged). Proofs remain `sorry`.
-- Functions carrying a nontrivial postcondition (10): `root`, `left`, `right`, `parent`,
-- `direct_path`, `TreeNodeIndex::{new, u32}`, `TreeSize::{new, inc, dec}`.
-- True posts (9): `sibling`, `copath`, `lowest_common_ancestor`, `common_direct_path`,
-- `is_node_in_tree`, `LeafNodeIndex::{to_tree_index, from_tree_index}`,
-- `ParentNodeIndex::{to_tree_index, from_tree_index}`.
-- Gone since the previous census: `level`, `TreeSize::leaf_count`.
-- This file is a reference view; it is not imported by `Proofs.lean` — but `Proofs.lean`'s
-- theorem statements must correspond 1:1 to the statements below (same names, same triples).
import Aeneas
import CoreModels
import Openmls.Extraction.Types
import Openmls.Extraction.Funs
import Openmls.Extraction.Specs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace openmls

@[spec]
theorem binary_tree.array_representation.treemath.root.spec.proof
  (size : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.root size
  ⦃ ⇓ res =>
  ⌜ (binary_tree.array_representation.treemath.root.post size res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.left.spec.proof
  (index : binary_tree.array_representation.treemath.ParentNodeIndex) :
  (binary_tree.array_representation.treemath.left.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.left index
  ⦃ ⇓ res =>
  ⌜ (binary_tree.array_representation.treemath.left.post index res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.right.spec.proof
  (index : binary_tree.array_representation.treemath.ParentNodeIndex) :
  (binary_tree.array_representation.treemath.right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.right index
  ⦃ ⇓ res =>
  ⌜ (binary_tree.array_representation.treemath.right.post index res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.parent.spec.proof
  (x : binary_tree.array_representation.treemath.TreeNodeIndex) :
  (binary_tree.array_representation.treemath.parent.pre x).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.parent x
  ⦃ ⇓ res =>
  ⌜ (binary_tree.array_representation.treemath.parent.post x res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.sibling.spec.proof
  (index : binary_tree.array_representation.treemath.TreeNodeIndex) :
  (binary_tree.array_representation.treemath.sibling.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.sibling index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.direct_path.spec.proof
   (node_index : binary_tree.array_representation.treemath.LeafNodeIndex)
  (size : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.direct_path.pre node_index
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.direct_path node_index size
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.direct_path.post node_index size
  res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.copath.spec.proof
  (leaf_index : binary_tree.array_representation.treemath.LeafNodeIndex)
  (size : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.copath.pre leaf_index size).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.copath leaf_index size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem
  binary_tree.array_representation.treemath.lowest_common_ancestor.spec.proof
   (x : binary_tree.array_representation.treemath.LeafNodeIndex)
  (y : binary_tree.array_representation.treemath.LeafNodeIndex) :
  (binary_tree.array_representation.treemath.lowest_common_ancestor.pre x
  y).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.lowest_common_ancestor x y
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.common_direct_path.spec.proof
   (x : binary_tree.array_representation.treemath.LeafNodeIndex)
  (y : binary_tree.array_representation.treemath.LeafNodeIndex)
  (size : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.common_direct_path.pre x y
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.common_direct_path x y size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.is_node_in_tree.spec.proof
   (node_index : binary_tree.array_representation.treemath.TreeNodeIndex)
  (size : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.is_node_in_tree.pre node_index
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.is_node_in_tree node_index size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem
  binary_tree.array_representation.treemath.LeafNodeIndex.to_tree_index.spec.proof
   (self : binary_tree.array_representation.treemath.LeafNodeIndex) :
  (binary_tree.array_representation.treemath.LeafNodeIndex.to_tree_index.pre
  self).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.LeafNodeIndex.to_tree_index self
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem
  binary_tree.array_representation.treemath.LeafNodeIndex.from_tree_index.spec.proof
   (node_index : Std.U32) :
  (binary_tree.array_representation.treemath.LeafNodeIndex.from_tree_index.pre
  node_index).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.LeafNodeIndex.from_tree_index
  node_index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem
  binary_tree.array_representation.treemath.ParentNodeIndex.to_tree_index.spec.proof
   (self : binary_tree.array_representation.treemath.ParentNodeIndex) :
  (binary_tree.array_representation.treemath.ParentNodeIndex.to_tree_index.pre
  self).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.ParentNodeIndex.to_tree_index self
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem
  binary_tree.array_representation.treemath.ParentNodeIndex.from_tree_index.spec.proof
   (node_index : Std.U32) :
  (binary_tree.array_representation.treemath.ParentNodeIndex.from_tree_index.pre
  node_index).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.ParentNodeIndex.from_tree_index
  node_index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.TreeNodeIndex.new.spec.proof
   (index : Std.U32) :
  (binary_tree.array_representation.treemath.TreeNodeIndex.new.pre index).holds
  →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.TreeNodeIndex.new index
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.TreeNodeIndex.new.post index
  res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.TreeNodeIndex.u32.spec.proof
   (self : binary_tree.array_representation.treemath.TreeNodeIndex) :
  (binary_tree.array_representation.treemath.TreeNodeIndex.u32.pre self).holds
  →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.TreeNodeIndex.u32 self
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.TreeNodeIndex.u32.post self
  res).holds ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.TreeSize.new.spec.proof
   (nodes : Std.U32) :
  (binary_tree.array_representation.treemath.TreeSize.new.pre nodes).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.TreeSize.new nodes
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.TreeSize.new.post nodes res).holds
  ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.TreeSize.inc.spec.proof
   (self : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.TreeSize.inc.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.TreeSize.inc self
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.TreeSize.inc.post self res).holds
  ⌝ ⦄
  := by sorry

@[spec]
theorem binary_tree.array_representation.treemath.TreeSize.dec.spec.proof
   (self : binary_tree.array_representation.treemath.TreeSize) :
  (binary_tree.array_representation.treemath.TreeSize.dec.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  binary_tree.array_representation.treemath.TreeSize.dec self
  ⦃ ⇓ res =>
  ⌜
  (binary_tree.array_representation.treemath.TreeSize.dec.post self res).holds
  ⌝ ⦄
  := by sorry

end openmls
