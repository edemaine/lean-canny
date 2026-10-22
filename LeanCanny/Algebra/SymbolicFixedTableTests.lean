/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableSubresultants

/-! # A common ordinary evaluation recognizes every symbolic table test

The reference exponent is independent of direction choices. A table accepted
at that evaluation is valid over the symbolic fraction field, with no need
to equate a first-success choice with the native last-success search.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical

theorem Budget.discriminant_map_zero_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) :
    (p.map (scalarEvaluation beta)).resultant (p.map (scalarEvaluation beta)).derivative = 0 ↔
      discriminant p = 0 := by
  have hd := B.degree_map p hp beta hb he
  have hdd : (p.derivative.map (scalarEvaluation beta)).natDegree = p.derivative.natDegree := by
    rw [← derivative_map, natDegree_derivative, hd, natDegree_derivative]
  rw [← discriminant_map _ _ hd hdd]
  exact B.discriminant_zero_iff p hp beta hb he

theorem Budget.separable_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p) (hn : p ≠ 0)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) :
    (p.map (scalarEvaluation beta)).Separable ↔ (p.map embedding).Separable := by
  have hs : p.map (scalarEvaluation beta) ≠ 0 := by
    intro hz
    have hc := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hz
    rw [coeff_map, coeff_zero] at hc
    exact (leadingCoeff_ne_zero.mpr hn) ((B.coefficient_zero_iff p hp beta hb he _).mp hc)
  rw [SymbolicPrimitivePair.separable_iff_discriminant _ hs,
    SymbolicPrimitivePair.separable_iff_discriminant _ ((Polynomial.map_ne_zero_iff embedding_injective).mpr hn)]
  have hf : (p.map embedding).resultant (p.map embedding).derivative = 0 ↔ discriminant p = 0 := by
    rw [← discriminant_map embedding p (natDegree_map_eq_of_injective embedding_injective _)
      (natDegree_map_eq_of_injective embedding_injective _)]
    exact map_eq_zero_iff embedding embedding_injective
  exact not_congr ((B.discriminant_map_zero_iff p hp beta hb he).trans hf.symm)

theorem Budget.resultant_test_iff (B : Budget) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : B.Controls p) (hq : B.Controls q) (hc : c ≤ B.directionLimit)
    (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (B.testExponent + B.pair.testExponent)) :
    (cannyResultant (p.map (scalarEvaluation beta)) (q.map (scalarEvaluation beta)) c).resultant
        (cannyResultant (p.map (scalarEvaluation beta)) (q.map (scalarEvaluation beta)) c).derivative = 0 ↔
      discriminant (cannyResultant p q c) = 0 := by
  have hec : beta ≤ InfinitesimalSign.dyadic B.testExponent :=
    he.trans (dyadic_antitone (Nat.le_add_right _ _))
  have hep : beta ≤ InfinitesimalSign.dyadic B.pair.testExponent :=
    he.trans (dyadic_antitone (Nat.le_add_left _ _))
  rw [← resultant_map_of_degrees (scalarEvaluation beta) p q c
    (B.degree_map p hp beta hb hec) (B.degree_map q hq beta hb hec)]
  exact B.pair.discriminant_map_zero_iff _ (B.pair_controls p q c hp hq hc) beta hb hep

theorem node_map (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height h i : ℕ) (hh : h ≤ height)
    (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height)) :
    (node a c h i).map (scalarEvaluation beta) =
      node (fun i => (a i).map (scalarEvaluation beta)) c h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih =>
    simp only [node]
    rw [resultant_map_of_degrees (scalarEvaluation beta) _ _ _
      (node_degree_map B a c ha hc height h (2 * i) (by omega) beta hb he)
      (node_degree_map B a c ha hc height h (2 * i + 1) (by omega) beta hb he),
      ih (2 * i) (by omega), ih (2 * i + 1) (by omega)]

theorem node_separable_iff (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height h i : ℕ) (hh : h ≤ height)
    (hn : node a c h i ≠ 0) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height)) :
    ((node a c h i).map (scalarEvaluation beta)).Separable ↔ ((node a c h i).map embedding).Separable := by
  exact Budget.separable_iff _ _ (node_controls B a c ha hc h i) hn beta hb
    (he.trans (dyadic_antitone (testExponent_le_reference B height h hh)))

theorem node_generic_separable_of_evaluation (B : Budget) (a : ℕ → Polynomial Coefficient)
    (c : ℕ → ℕ → ℕ) (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c)
    (height h i : ℕ) (hh : h ≤ height) (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height))
    (hs : (node (fun i => (a i).map (scalarEvaluation beta)) c h i).Separable) :
    ((node a c h i).map embedding).Separable := by
  have hm := node_map B a c ha hc height h i hh beta hb he
  rw [← hm] at hs
  have hn : node a c h i ≠ 0 := by intro hz; rw [hz, Polynomial.map_zero] at hs; exact hs.ne_zero rfl
  exact (node_separable_iff B a c ha hc height h i hh hn beta hb he).mp hs

end LeanCanny.Algebra.SymbolicFixedTable
