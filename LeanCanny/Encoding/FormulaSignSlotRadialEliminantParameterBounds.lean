/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientModel
public import LeanCanny.Algebra.PartialDerivativeDegree
/-! # Original degree bounds for the actual tilted row parameters

The dense coefficient comes from the original squared integer source. Radius
and center exponents therefore remain bounded by twice its original degree;
the two sparse perturbation terms introduce no center or radius powers.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterBounds
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantCoefficientModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalInput.polynomial

theorem dense_bounds (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ)
    (r : ℕ) (v : Fin (d c) →₀ ℕ) (H : dense c j e r v ≠ 0) :
    r ≤ 2 * degreeBudget c ∧ ∀ i, v i ≤ 2 * degreeBudget c := by
  let p := pderiv (FormulaSignSlotRadialFormalInput.spatialIndex c j)
    ((FormulaSignSlotRadialFormalInput.polynomial c) ^ 2)
  have HP : p.totalDegree ≤ 2 * degreeBudget c :=
    ((PartialDerivativeDegree.degree_le _ _).trans (Nat.sub_le _ _)).trans
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2
        (FormulaSignSlotRadialFormalInput.polynomial_degree c)))
  have HC : FormulaSignSlotRadialEliminantSource.exponent c e r v ∈ p.support :=
    mem_support_iff.mpr H
  have HB (i : Fin (FormulaSignSlotRadialFormalInput.dimension c)) :
      FormulaSignSlotRadialEliminantSource.exponent c e r v i ≤ 2 * degreeBudget c :=
    ((monomial_le_degreeOf i HC).trans (degreeOf_le_totalDegree _ i)).trans HP
  constructor
  · have HH := HB (FormulaSignSlotRadialEliminantSource.layout c (.inl 0))
    simpa only [FormulaSignSlotRadialEliminantSource.exponent, Finsupp.mapDomain_equiv_apply,
      Equiv.symm_apply_apply, NestedPolynomial.joinExponent, Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply,
      Finsupp.sumElim_inl, IntegerParameterFlatten.joinExponent_zero] using HH
  · intro i
    have HH := HB (FormulaSignSlotRadialEliminantSource.layout c (.inr i))
    simpa only [FormulaSignSlotRadialEliminantSource.exponent, Finsupp.mapDomain_equiv_apply,
      Equiv.symm_apply_apply, NestedPolynomial.joinExponent, Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply,
      Finsupp.sumElim_inr] using HH

theorem gradient_bounds (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) (H : gradient c j e s t r v ≠ 0) :
    s ≤ 2 ∧ t = 0 ∧ r ≤ 2 * degreeBudget c ∧ ∀ i, v i ≤ 2 * degreeBudget c := by
  have HS : s ≤ 2 := by
    by_contra HN
    have H0 : s ≠ 0 := by omega
    have H1 : s ≠ 1 := by omega
    have H2 : s ≠ 2 := by omega
    simp [gradient, kernel, H0, H1, H2] at H
  have HT : t = 0 := by
    by_contra HN
    simp [gradient, kernel, HN] at H
  have HD : r ≤ 2 * degreeBudget c ∧ ∀ i, v i ≤ 2 * degreeBudget c := by
    by_cases HZ : dense c j e.some r v ≠ 0
    · exact dense_bounds c j e.some r v HZ
    · have HH : r = 0 ∧ v = 0 := by
        by_contra HN
        simp [gradient, kernel, not_ne_iff.mp HZ, HN] at H
      rcases HH with ⟨rfl, rfl⟩
      exact ⟨Nat.zero_le _, fun _ => Nat.zero_le _⟩
  exact ⟨HS, HT, HD⟩

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterBounds
