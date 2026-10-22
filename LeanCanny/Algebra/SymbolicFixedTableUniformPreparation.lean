/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableUniform

/-! # Integer table preparation at a binary-FP source reference

Any sufficiently small reference evaluation works. In particular the closed
source exponent, whose binary writer is polynomial time, determines actual
integer last-success metadata for the symbolic tree.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

structure Reference (B : Budget) (height : ℕ) where
  exponent : ℕ
  sufficient : preparationExponent B height ≤ exponent

def sourceReference (B : Budget) (n : ℕ) : Reference B n.size :=
  ⟨sourceExponent B.degree B.innerDegree B.massExponent n, preparationExponent_le_source B n⟩

namespace Reference

theorem leaf_sufficient {B : Budget} {height : ℕ} (R : Reference B height) : B.testExponent ≤ R.exponent :=
  (Nat.le_add_right _ _).trans R.sufficient

theorem tree_sufficient {B : Budget} {height : ℕ} (R : Reference B height) :
    referenceExponent B.squarefree height ≤ R.exponent := (Nat.le_add_left _ _).trans R.sufficient

noncomputable def leaves {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) : ℕ → SeparableIntegerPolynomial :=
  integerLeaves B a ha hn R.exponent R.leaf_sufficient

noncomputable def directions {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) : ℕ → ℕ → ℕ :=
  integerDirections (R.leaves a ha hn)

theorem admissible {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) :
    Admissible B.squarefree (R.directions a ha hn) :=
  integerDirections_admissible _ _ (integerLeaves_degree B a ha hn _ _)

theorem node_associated {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (h i : ℕ) (hh : h ≤ height) :
    Associated ((node (fun i => SymbolicScaledSquarefree.polynomial (a i))
      (R.directions a ha hn) h i).map (scalarEvaluation (InfinitesimalSign.dyadic R.exponent)))
      ((BalancedPrimitiveTree.node (R.leaves a ha hn) h i).polynomial.map (Int.castRingHom ℝ)) := by
  rw [node_map B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i)) (R.admissible a ha hn)
    height h i hh _ (by unfold InfinitesimalSign.dyadic; positivity) (dyadic_antitone R.tree_sufficient),
    ← integer_node_eq, node_map_injective (Int.castRingHom ℝ) (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
  exact SymbolicFixedTable.node_associated _ _ _ (fun i =>
    (B.cleared_squarefree_associated _ (ha i) (hn i) _ R.leaf_sufficient).symm) h i

theorem generic_separable {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (h i : ℕ) (hh : h ≤ height) :
    ((node (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) h i).map embedding).Separable := by
  have hs := (R.node_associated a ha hn h i hh).symm.separable
    ((BalancedPrimitiveTree.node (R.leaves a ha hn) h i).separable_in_field (L := ℝ))
  have hne : node (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) h i ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hs
    exact hs.ne_zero rfl
  exact (node_separable_iff B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (R.admissible a ha hn) height h i hh hne _ (by unfold InfinitesimalSign.dyadic; positivity)
    (dyadic_antitone R.tree_sufficient)).mp hs

theorem node_degree {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (h i : ℕ) (hh : h ≤ height) :
    (BalancedPrimitiveTree.node (R.leaves a ha hn) h i).polynomial.natDegree =
      (node (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) h i).natDegree := by
  have hd := PrincipalSubresultant.natDegree_eq_of_associated (R.node_associated a ha hn h i hh)
  rw [natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)] at hd
  exact hd.symm.trans (node_degree_map B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (R.admissible a ha hn) height h i hh _ (by unfold InfinitesimalSign.dyadic; positivity)
    (dyadic_antitone R.tree_sufficient))

theorem separableTable {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0) :
    SeparableTable (fun i => SymbolicScaledSquarefree.polynomial (a i)) (R.directions a ha hn) height :=
  fun h i hh => R.generic_separable a ha hn h i hh

noncomputable def rootEquiv {B : Budget} {height : ℕ} (R : Reference B height)
    (a : ℕ → Polynomial Coefficient) (ha : ∀ i, B.Controls (a i)) (hn : ∀ i, a i ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic R.exponent)
    (h i : ℕ) (hh : h ≤ height) :
    {theta : ℝ // (node (fun i => SymbolicScaledSquarefree.polynomial (a i))
      (R.directions a ha hn) h i).eval₂ (scalarEvaluation beta) theta = 0} ≃ {x : Values ℝ h // valid a beta h i x} :=
  (SymbolicFixedTable.rootEquiv B.squarefree _ _ (fun i => B.squarefree_controls _ (ha i))
    (R.admissible a ha hn) height (R.separableTable a ha hn) beta hb
    (he.trans (dyadic_antitone R.tree_sufficient)) h i hh).trans
    (Equiv.subtypeEquivProp (funext fun x => propext (valid_squarefree_iff B a ha hn beta hb
      (he.trans (dyadic_antitone R.leaf_sufficient)) h i x)))

end Reference

end LeanCanny.Algebra.SymbolicFixedTable
