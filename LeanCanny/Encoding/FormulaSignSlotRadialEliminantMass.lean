/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantScalarMass
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantPacked
public import LeanCanny.Algebra.MacaulayNormalizedPolynomialMass
/-! # Original-only mass of the actual normalized formal eliminant

Every retained parameter is kept in the actual packed source. The bound uses
the monic characteristic quotient and requires no surviving extraneous determinant.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantMass
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantPackingLayout
open FormulaSignSlotRadialEliminantCoefficientModel
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MacaulayUniversal.polynomialValue

theorem nested_abs (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    ((((((FormulaSignSlotRadialEliminantRows.system c coordinate row).coeff e).coeff s).coeff t).coeff r).coeff v).natAbs ≤
      2 ^ FormulaSignSlotRadialEliminantScalarMass.budget c := by
  let f := e.mapDomain (CoerciveCriticalHomogenization.layout (n := FormulaSignSlotRadialFormalInput.spatial c)).symm
  have HF : f.mapDomain CoerciveCriticalHomogenization.layout = e := by
    ext i
    simp only [f, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have HR := FormulaSignSlotRadialEliminantRows.coefficient c coordinate row
    (f.mapDomain CoerciveCriticalHomogenization.layout) s t r v
  have HN := congrArg (fun u : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ =>
    (((((FormulaSignSlotRadialEliminantRows.system c coordinate row).coeff u).coeff s).coeff t).coeff r).coeff v) HF
  have HB : ((FormulaSignSlotRadialEliminantRows.polynomial c coordinate row).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (f.mapDomain CoerciveCriticalHomogenization.layout) s t r v)).natAbs ≤
        FormulaSignSlotRadialEliminantScalarMass.denseBound c + 2 * degreeBudget c + 3 := by
    cases HT : CoerciveCriticalHomogenization.layout.symm row with
    | none =>
      have HE : row = CoerciveCriticalHomogenization.layout none := by rw [← HT, Equiv.apply_symm_apply]
      rw [HE]
      exact (FormulaSignSlotRadialEliminantScalarMass.coordinate_abs c coordinate f s t r v).trans (by omega)
    | some j =>
      have HE : row = CoerciveCriticalHomogenization.layout (some j) := by rw [← HT, Equiv.apply_symm_apply]
      rw [HE, gradient_eq]
      exact FormulaSignSlotRadialEliminantScalarMass.gradient_abs c j f s t r v
  exact (congrArg Int.natAbs (HR.trans HN)).symm.le.trans
    (HB.trans (FormulaSignSlotRadialEliminantScalarMass.scalar_budget c))

private theorem exponent_roundtrip {a : ℕ} (f : Fin (a + 3) →₀ ℕ) :
    TriplePolynomialParameterFlatten.exponent (f 0) (f.tail 0) (f.tail.tail 0) f.tail.tail.tail = f := by
  simp only [TriplePolynomialParameterFlatten.exponent, Finsupp.cons_tail]

theorem parameter_abs (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ)
    (f : Fin (d c + 3) →₀ ℕ) :
    (((FormulaSignSlotRadialEliminantParameterRows.row c coordinate row).coeff e).coeff f).natAbs ≤
      2 ^ FormulaSignSlotRadialEliminantScalarMass.budget c := by
  have H := FormulaSignSlotRadialEliminantParameterRows.coefficient c coordinate row e
    (f 0) (f.tail 0) (f.tail.tail 0) f.tail.tail.tail
  rw [exponent_roundtrip f] at H
  rw [H]
  exact nested_abs c coordinate row e _ _ _ _

noncomputable def rowBudget (c : List Bool) : ℕ :=
  parameterWidth c * (d (pairFst c) + 3) + FormulaSignSlotRadialEliminantScalarMass.budget (pairFst c)

theorem rowBudget_unary : UnaryFn rowBudget :=
  (parameterWidth_unary.mul ((FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add
    (UnaryFn.const 3))).add (FormulaSignSlotRadialEliminantScalarMass.budget_unary.comp pairFst_mem_FP)

theorem row_mass (c : List Bool) (row : Fin (spatial c + 1))
    (e : Fin (spatial c + 1) →₀ ℕ) :
    coefficientMass ((FormulaSignSlotRadialEliminantPacked.system c row).coeff e) ≤ 2 ^ rowBudget c := by
  rw [FormulaSignSlotRadialEliminantPacked.system, coeff_map,
    FixedWidthKronecker.encode_eq_sum _ _ _ (FormulaSignSlotRadialEliminantPacked.row_support c row e)]
  apply (coefficientMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin (FixedWidthPolynomial.count (d (pairFst c) + 3) (parameterWidth c)),
        2 ^ FormulaSignSlotRadialEliminantScalarMass.budget (pairFst c) := by
      apply Finset.sum_le_sum
      intro k _
      rw [coefficientMass_monomial]
      exact parameter_abs (pairFst c) _ row e _
    _ = 2 ^ rowBudget c := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        FixedWidthPolynomial.count, ← pow_mul, ← pow_add, rowBudget]

noncomputable def resultBudget (c : List Bool) : ℕ :=
  PaddedCharacteristicQuotientMass.budget (columns c) (columns c) (rowBudget c)

theorem resultBudget_binary : BinaryFn resultBudget :=
  PaddedCharacteristicQuotientMass.budget_binary columns_binary columns_binary (BinaryFn.ofUnary rowBudget_unary)

theorem eliminant_mass (c : List Bool) :
    coefficientMass (FormulaSignSlotRadialEliminantPacked.eliminant c) ≤ 2 ^ resultBudget c := by
  have H := MacaulayNormalizedPolynomialMass.normalized_value
    (FormulaSignSlotRadialEliminantPacked.system c)
    (CoerciveCriticalHomogenization.finDegree (sourceDegree c)) (width c) (rowBudget c)
    (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
    (FormulaSignSlotRadialEliminantPacked.homogeneous c)
    (CoerciveCriticalHomogenization.finDegree_pos _) (row_mass c)
  rw [FormulaSignSlotRadialEliminantPacked.polynomialValue] at H
  exact H

theorem coefficient_abs (c : List Bool) (k : Fin (FormulaSignSlotRadialEliminantPacked.parameterBox c)) :
    ((FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff
        (FixedWidthPolynomial.vector (d (pairFst c) + 3) (parameterWidth c) k)).natAbs ≤ 2 ^ resultBudget c := by
  rw [← FormulaSignSlotRadialEliminantPacked.eliminant_coefficient]
  exact (coeff_natAbs_le_coefficientMass _ _).trans (eliminant_mass c)

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantMass
