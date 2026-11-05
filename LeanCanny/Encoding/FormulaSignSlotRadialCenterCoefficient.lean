/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantFormalMass
public import LeanCanny.Algebra.PhysicalCriticalMassBudget
/-! # Actual formal-center coefficient polynomials of the radial eliminant

Perturbation, target and radius indices select coefficients. Every center
variable remains an integer variable; specialization never assumes integer
height bounds for real coefficients.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantPackingLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

noncomputable def polynomial (c : List Bool) (s t r : ℕ) : MvPolynomial (Fin (d (pairFst c))) ℤ :=
  (((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
    (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff s).coeff t).coeff r

theorem coefficient_weight (c : List Bool) (s t r : ℕ) (v : Fin (d (pairFst c)) →₀ ℕ)
    (hv : (polynomial c s t r).coeff v ≠ 0) :
    s + t + r + v.sum (fun _ e => e) ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c := by
  have HC : (FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff
        (TriplePolynomialParameterFlatten.exponent s t r v) ≠ 0 := by
    change (TriplePolynomialParameterFlatten.flatten _).coeff _ ≠ 0
    rw [TriplePolynomialParameterFlatten.coefficient]
    exact hv
  have H := (le_totalDegree (mem_support_iff.mpr HC)).trans
    (FormulaSignSlotRadialEliminantPacked.result_degree c)
  simpa only [TriplePolynomialParameterFlatten.exponent, Finsupp.sum_cons, Nat.add_assoc] using H

theorem degree (c : List Bool) (s t r : ℕ) :
    (polynomial c s t r).totalDegree ≤ FormulaSignSlotRadialEliminantPacked.resultDegree c := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro v hv
  have H := coefficient_weight c s t r v (mem_support_iff.mp hv)
  omega

theorem zero_of_large_index (c : List Bool) (s t r : ℕ)
    (h : FormulaSignSlotRadialEliminantPacked.resultDegree c < s ∨
      FormulaSignSlotRadialEliminantPacked.resultDegree c < t ∨
      FormulaSignSlotRadialEliminantPacked.resultDegree c < r) : polynomial c s t r = 0 := by
  ext v
  change (polynomial c s t r).coeff v = 0
  by_contra H
  have HH := coefficient_weight c s t r v H
  rcases h with h | h | h <;> omega

noncomputable def massBudget (c : List Bool) :=
  d (pairFst c) * parameterWidth c + FormulaSignSlotRadialEliminantFormalMass.budget c

theorem massBudget_binary : BinaryFn massBudget :=
  (BinaryFn.ofUnary ((FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).mul
    parameterWidth_unary)).add FormulaSignSlotRadialEliminantFormalMass.budget_binary

theorem mass (c : List Bool) (s t r : ℕ) : MvMass.mass (polynomial c s t r) ≤ 2 ^ massBudget c := by
  apply PhysicalCriticalMassBudget.coefficient_box
  · intro v hv i
    exact ((monomial_le_degreeOf i hv).trans ((degreeOf_le_totalDegree _ i).trans
      (degree c s t r))).trans_lt (FormulaSignSlotRadialEliminantPacked.result_fit c)
  · exact FormulaSignSlotRadialEliminantFormalMass.nested_abs c s t r

theorem specialization (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (s t r : ℕ) :
    ((((FormulaSignSlotRadialParameterEliminant.eliminant (pairFst c) a
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff s).coeff t).coeff r) =
        (polynomial c s t r).eval₂ (Int.castRingHom ℝ) a := by
  rw [FormulaSignSlotRadialFormalEliminant.coefficient_specialization]
  simp only [Polynomial.coeff_map, FormulaSignSlotRadialFormalCenter.radiusMap,
    Polynomial.coe_mapRingHom]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
