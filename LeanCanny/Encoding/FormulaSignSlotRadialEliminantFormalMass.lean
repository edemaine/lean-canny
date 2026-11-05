/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantMass
public import LeanCanny.Algebra.FixedWidthTarskiMass
/-! # Uniform integer heights of every retained formal eliminant coefficient -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantFormalMass
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantPackingLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def budget (c : List Bool) : ℕ :=
  (d (pairFst c) + 3) * parameterWidth c + FormulaSignSlotRadialEliminantMass.resultBudget c

theorem budget_binary : BinaryFn budget :=
  (BinaryFn.ofUnary (((FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add
    (UnaryFn.const 3)).mul parameterWidth_unary)).add FormulaSignSlotRadialEliminantMass.resultBudget_binary

theorem degree_binary : BinaryFn FormulaSignSlotRadialEliminantPacked.resultDegree :=
  (columns_binary.add (BinaryFn.const 1)).mul
    (columns_binary.mul (BinaryFn.ofUnary parameterDegree_unary))

theorem parameter_mass (c : List Bool) :
    MvMass.mass (FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)) ≤ 2 ^ budget c := by
  apply FixedWidthTarskiMass.mass_le_pow
  · intro f hf i
    exact ((monomial_le_degreeOf i hf).trans ((degreeOf_le_totalDegree _ i).trans
      (FormulaSignSlotRadialEliminantPacked.result_degree c))).trans_lt
        (FormulaSignSlotRadialEliminantPacked.result_fit c)
  · exact FormulaSignSlotRadialEliminantMass.eliminant_mass c

theorem coefficient_abs (c : List Bool) (f : Fin (d (pairFst c) + 3) →₀ ℕ) :
    ((FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff f).natAbs ≤ 2 ^ budget c :=
  (MvMass.coeff_le _ _).trans (parameter_mass c)

theorem nested_abs (c : List Bool) (s t r : ℕ) (v : Fin (d (pairFst c)) →₀ ℕ) :
    (((((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff s).coeff t).coeff r).coeff v).natAbs ≤
        2 ^ budget c := by
  have H := coefficient_abs c (TriplePolynomialParameterFlatten.exponent s t r v)
  change ((TriplePolynomialParameterFlatten.flatten
    (FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
      (FormulaSignSlotRadialEliminantInput.coordinate c))).coeff
        (TriplePolynomialParameterFlatten.exponent s t r v)).natAbs ≤ _ at H
  rw [TriplePolynomialParameterFlatten.coefficient] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantFormalMass
