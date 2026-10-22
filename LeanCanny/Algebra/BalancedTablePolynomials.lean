/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedMetadataTable
public import LeanCanny.Algebra.CannyResultantDegrees
public import LeanCanny.Algebra.ScaledSquarefreeSpace
public import LeanCanny.Algebra.SeparableReaderReindex

/-! # The polynomial tree defined by a supplied metadata table

Leaves use the scaled square-free original indexed polynomial. Internal nodes
use the table's supplied child orders and direction. All tables define a tree;
metadata consistency is needed only to identify it with the canonical primitive
tree, not to define its coefficient computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet child original height index)

def leafInput (s : List Bool) : List Bool :=
  pair (BalancedMetadataTable.source (original (pairFst s))) (BinaryNat.normalize (BalancedParameterContext.indexWord (pairFst s)))

attribute [local irreducible] BinaryNat.normalize

theorem leafInput_FP : leafInput ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP BalancedParameterContext.original_FP) BalancedMetadataTable.source_FP
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP BalancedParameterContext.indexWord_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_pair hc hi

theorem leafInput_eq (s : List Bool) :
    leafInput s = pair (BalancedMetadataTable.source (original (pairFst s))) (BinaryNatCode.encode (index (pairFst s))) := by
  simp only [leafInput, BinaryNat.normalize_eq_bits, index, BinaryNatCode.encode]

noncomputable def leafFamily (B : Family) : Family := B.reindex leafInput
noncomputable def leafReaders (B : Family) (A : Readers B) : Readers (leafFamily B) := A.reindex leafInput leafInput_FP

noncomputable def tree (B : Family) (c : List Bool) : ℕ → ℕ → Polynomial ℤ
  | 0, i => ScaledSquarefree.polynomial (B.polynomial (pair (BalancedMetadataTable.source c) (BinaryNatCode.encode i)))
  | h + 1, i => cannyResultantWithDegrees (tree B c h (2 * i)) (tree B c h (2 * i + 1))
      (BalancedMetadataTable.direction (packet c (h + 1) i))
      (BalancedMetadataTable.order (packet c h (2 * i))) (BalancedMetadataTable.order (packet c h (2 * i + 1)))

noncomputable def node (B : Family) (p : List Bool) : Polynomial ℤ := tree B (original p) (height p) (index p)

theorem node_packet (B : Family) (c : List Bool) (h i : ℕ) : node B (packet c h i) = tree B c h i := by
  simp only [node, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet, BalancedParameterContext.index_packet]

theorem node_zero (B : Family) (p : List Bool) (hh : height p = 0) :
    node B p = ScaledSquarefree.polynomial (B.polynomial
      (pair (BalancedMetadataTable.source (original p)) (BinaryNatCode.encode (index p)))) := by
  simp only [node, hh, tree]

theorem node_children (B : Family) (p : List Bool) (hh : 0 < height p) :
    node B p = cannyResultantWithDegrees (node B (child false p)) (node B (child true p))
      (BalancedMetadataTable.direction p) (BalancedMetadataTable.order (child false p)) (BalancedMetadataTable.order (child true p)) := by
  obtain ⟨h, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  have hd := BalancedMetadataTable.read_eq_packet true p
  have hl := BalancedMetadataTable.read_eq_packet false (child false p)
  have hr := BalancedMetadataTable.read_eq_packet false (child true p)
  unfold BalancedMetadataTable.direction BalancedMetadataTable.order
  rw [hd, hl, hr]
  simp only [node, BalancedParameterContext.original_child, BalancedParameterContext.height_child,
    BalancedParameterContext.index_child, he, Nat.succ_sub_one, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
  rfl

/-- Finite consistency conditions for one rooted subtree. -/
def Consistent (B : Family) (c : List Bool) (leaves : ℕ → SeparableIntegerPolynomial) : ℕ → ℕ → Prop
  | 0, i => ScaledSquarefree.polynomial (B.polynomial
      (pair (BalancedMetadataTable.source c) (BinaryNatCode.encode i))) = (leaves i).polynomial
  | h + 1, i => Consistent B c leaves h (2 * i) ∧ Consistent B c leaves h (2 * i + 1) ∧
      BalancedMetadataTable.order (packet c h (2 * i)) = (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial.natDegree ∧
      BalancedMetadataTable.order (packet c h (2 * i + 1)) = (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial.natDegree ∧
      BalancedMetadataTable.direction (packet c (h + 1) i) = PrimitivePair.select
        (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial

theorem tree_eq_node (B : Family) (c : List Bool) (leaves : ℕ → SeparableIntegerPolynomial) (h i : ℕ)
    (hc : Consistent B c leaves h i) : tree B c h i = (BalancedPrimitiveTree.node leaves h i).polynomial := by
  induction h generalizing i with
  | zero => exact hc
  | succ h ih =>
    obtain ⟨hl, hr, hd, he, hs⟩ := hc
    rw [tree, ih _ hl, ih _ hr, hd, he, hs, cannyResultantWithDegrees_exact]
    rfl

end LeanCanny.Algebra.BalancedTablePolynomials
