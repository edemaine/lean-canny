/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSlice
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSelection
public import LeanCanny.Algebra.MvTwoParameterEvaluation
/-! # The selected formal slice evaluates to the actual radial grid equation -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialGridSliceEvaluation
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem slice (c : List Bool) (tau t r : ℕ) :
    MvTwoParameterCoefficient.slice (FormulaSignSlotRadialGridSlice.polynomial c tau) t r =
      FormulaSignSlotRadialCenterCoefficient.polynomial c tau t r := by
  ext v
  rw [MvTwoParameterCoefficient.coefficient, FormulaSignSlotRadialGridSlice.coefficient]

theorem parameter_specialization (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau : ℕ) :
    MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) a (FormulaSignSlotRadialGridSlice.polynomial c tau) =
      (FormulaSignSlotRadialParameterEliminant.eliminant (pairFst c) a
        (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau := by
  ext t r
  rw [MvTwoParameterCoefficient.selected_coefficient, slice]
  exact (FormulaSignSlotRadialCenterCoefficient.specialization c a tau t r).symm

theorem evaluation (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau : ℕ) (eta radius : ℝ) :
    (FormulaSignSlotRadialGridSlice.polynomial c tau).eval₂ (Int.castRingHom ℝ)
      (Fin.cons eta (Fin.cons radius a)) =
    ((FormulaSignSlotRadialParameterEliminant.eliminant (pairFst c) a
      (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau).eval₂ (Polynomial.evalRingHom radius) eta := by
  rw [←MvTwoParameterCoefficient.point_evaluate,parameter_specialization,RealIteratedTarski.evaluate_apply]

theorem selected (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau degree : ℕ)
    (H : FormulaSignSlotRadialCenterSelection.Guards c a tau degree) (eta radius : ℝ) :
    (FormulaSignSlotRadialGridSlice.polynomial c tau).eval₂ (Int.castRingHom ℝ)
      (Fin.cons eta (Fin.cons radius a)) =
    (FormulaSignSlotRadialParameterEliminant.coordinate (pairFst c) a
      (FormulaSignSlotRadialEliminantInput.coordinate c)).eval₂ (Polynomial.evalRingHom radius) eta := by
  have HT := ((FormulaSignSlotRadialCenterSelection.guards_iff c a tau degree).mp H).1
  rw [evaluation, HT]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialGridSliceEvaluation
