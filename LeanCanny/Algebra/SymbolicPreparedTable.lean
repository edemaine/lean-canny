/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedSubtreeLocality
public import LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
public import LeanCanny.Algebra.SymbolicPrimitivePairSpace

/-! # Correctness interfaces for prepared symbolic tables

The integer preparation retains literal leaf polynomials and its actual selected
directions. Node and pair specifications transfer those data to the total
symbolic coefficient algorithms without assuming anything about malformed tables.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding
open BalancedParameterContext (packet child)
open scoped Classical

/-- A consistent integer table computes the matching symbolic tree whenever
leaf polynomials, node degrees, and selected directions are retained exactly. -/
theorem tree_eq_of_consistent (L : List Bool → Polynomial Coefficient)
    (B : SeparableBits.Family) (c : List Bool) (leaves : ℕ → SeparableIntegerPolynomial)
    (a : ℕ → Polynomial Coefficient) (directions : ℕ → ℕ → ℕ) (H h i : ℕ) (hh : h ≤ H)
    (hc : BalancedTablePolynomials.Consistent B c leaves h i)
    (hdegree : ∀ h i, h ≤ H → (BalancedPrimitiveTree.node leaves h i).polynomial.natDegree =
      (SymbolicFixedTable.node a directions h i).natDegree)
    (hdirection : ∀ h i, directions h i = PrimitivePair.select
      (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial
      (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial)
    (hleaf : ∀ j < 2 ^ h, L (pair c (BinaryNatCode.encode (2 ^ h * i + j))) = a (2 ^ h * i + j)) :
    tree L c h i = SymbolicFixedTable.node a directions h i := by
  induction h generalizing i with
  | zero =>
    simpa only [pow_zero, one_mul, Nat.add_zero, tree, SymbolicFixedTable.node]
      using hleaf 0 (by decide)
  | succ h ih =>
    obtain ⟨hcl, hcr, hdl, hdr, hd⟩ := hc
    have hhl : h ≤ H := by omega
    have hL := ih (2 * i) hhl hcl (fun j hj => by
      have he : 2 ^ h * (2 * i) + j = 2 ^ (h + 1) * i + j := by rw [pow_succ]; ring
      rw [he]
      exact hleaf j (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    have hR := ih (2 * i + 1) hhl hcr (fun j hj => by
      have he : 2 ^ h * (2 * i + 1) + j = 2 ^ (h + 1) * i + (2 ^ h + j) := by rw [pow_succ]; ring
      rw [he]
      exact hleaf (2 ^ h + j) (by rw [pow_succ]; omega))
    rw [tree, hL, hR, hdl, hdr, hd, hdegree h (2 * i) hhl, hdegree h (2 * i + 1) hhl,
      ← hdirection h i, cannyResultantWithDegrees_exact]
    rfl

/-- Literal polynomial and exact degree metadata at one prepared node. -/
structure NodeSpec (L : List Bool → Polynomial Coefficient) (c : List Bool)
    (a : ℕ → Polynomial Coefficient) (directions : ℕ → ℕ → ℕ) (h i : ℕ) : Prop where
  polynomial_eq : tree L c h i = SymbolicFixedTable.node a directions h i
  order_eq : BalancedMetadataTable.order (packet c h i) = (SymbolicFixedTable.node a directions h i).natDegree

/-- The two children and the actual direction needed for primitive recovery. -/
structure PairSpec (L : List Bool → Polynomial Coefficient) (c : List Bool)
    (a : ℕ → Polynomial Coefficient) (directions : ℕ → ℕ → ℕ) (h i : ℕ) : Prop where
  left : NodeSpec L c a directions h (2 * i)
  right : NodeSpec L c a directions h (2 * i + 1)
  direction_eq : BalancedMetadataTable.direction (packet c (h + 1) i) = directions h i

/-- Pair recovery over any supplied parent context. This is total even when
its table is malformed; `PairSpec` is needed only for mathematical correctness. -/
noncomputable def pairFamily (L : List Bool → Polynomial Coefficient)
    (parent : List Bool → List Bool) : SymbolicFixedTableEntryBits.Family where
  left p := node L (child false (parent p))
  right p := node L (child true (parent p))
  leftOrder p := BalancedMetadataTable.order (child false (parent p))
  rightOrder p := BalancedMetadataTable.order (child true (parent p))
  direction p := BalancedMetadataTable.direction (parent p)

/-- A single pair specification supplies both degree guards and the exact
polynomial representatives used by the native recovery reader. -/
theorem PairSpec.fields {L : List Bool → Polynomial Coefficient} {c : List Bool}
    {a : ℕ → Polynomial Coefficient} {directions : ℕ → ℕ → ℕ} {h i : ℕ}
    (spec : PairSpec L c a directions h i) (parent : List Bool → List Bool)
    (p : List Bool) (hp : parent p = packet c (h + 1) i) (right : Bool) :
    let F := pairFamily L parent
    F.leftOrder p = (F.left p).natDegree ∧ F.rightOrder p = (F.right p).natDegree ∧
      SymbolicPairRecoveryBits.Family.coordinate F right p =
        SymbolicFixedTable.pairCoordinate right (SymbolicFixedTable.node a directions h (2 * i))
          (SymbolicFixedTable.node a directions h (2 * i + 1)) (directions h i) := by
  have hl : (pairFamily L parent).left p = SymbolicFixedTable.node a directions h (2 * i) := by
    simp only [pairFamily, hp, BalancedParameterContext.child_packet, Bool.false_eq_true,
      ite_false, Nat.add_zero, node_packet]
    exact spec.left.polynomial_eq
  have hr : (pairFamily L parent).right p = SymbolicFixedTable.node a directions h (2 * i + 1) := by
    simp only [pairFamily, hp, BalancedParameterContext.child_packet, ite_true, node_packet]
    exact spec.right.polynomial_eq
  have hm : (pairFamily L parent).leftOrder p = ((pairFamily L parent).left p).natDegree := by
    calc
      _ = BalancedMetadataTable.order (packet c h (2 * i)) := by
        simp only [pairFamily, hp, BalancedParameterContext.child_packet, Bool.false_eq_true,
          ite_false, Nat.add_zero]
      _ = _ := spec.left.order_eq
      _ = _ := congrArg Polynomial.natDegree hl.symm
  have hn : (pairFamily L parent).rightOrder p = ((pairFamily L parent).right p).natDegree := by
    calc
      _ = BalancedMetadataTable.order (packet c h (2 * i + 1)) := by
        simp only [pairFamily, hp, BalancedParameterContext.child_packet, ite_true]
      _ = _ := spec.right.order_eq
      _ = _ := congrArg Polynomial.natDegree hr.symm
  refine ⟨hm, hn, ?_⟩
  rw [SymbolicPairRecoveryBits.Family.coordinate_eq _ _ _ hm hn, hl, hr]
  have hd : (pairFamily L parent).direction p = directions h i := by
    simpa only [pairFamily, hp] using spec.direction_eq
  rw [hd]

end LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
