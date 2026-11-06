/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSlice
/-! # Literal radius polynomials of actual radial eliminant coefficients

Radius and every center coordinate remain formal integer variables.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHead
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (tau eta : ℕ) : MvPolynomial (Fin (d (pairFst c)+1)) ℤ :=
  MvTwoParameterCoefficient.one (FormulaSignSlotRadialGridSlice.polynomial c tau) eta

theorem coefficient (c : List Bool) (tau eta r : ℕ) (v : Fin (d (pairFst c)) →₀ ℕ) :
    (polynomial c tau eta).coeff (v.cons r)=
      (FormulaSignSlotRadialCenterCoefficient.polynomial c tau eta r).coeff v := by
  unfold polynomial MvTwoParameterCoefficient.one
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,FormulaSignSlotRadialGridSlice.coefficient]

theorem degree (c : List Bool) (tau eta : ℕ) : (polynomial c tau eta).totalDegree ≤
    FormulaSignSlotRadialEliminantPacked.resultDegree c :=
  (MvTwoParameterCoefficient.one_degree _ _).trans (FormulaSignSlotRadialGridSlice.degree c tau)
theorem mass (c : List Bool) (tau eta : ℕ) : MvMass.mass (polynomial c tau eta) ≤
    2^FormulaSignSlotRadialEliminantFormalMass.budget c :=
  (MvTwoParameterCoefficient.one_mass _ _).trans (FormulaSignSlotRadialGridSlice.mass c tau)
theorem fit (c : List Bool) (tau eta : ℕ) : (polynomial c tau eta).totalDegree <
    2^FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c :=
  (MvTwoParameterCoefficient.one_degree _ _).trans_lt (FormulaSignSlotRadialGridSlice.fit c tau)

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHead
