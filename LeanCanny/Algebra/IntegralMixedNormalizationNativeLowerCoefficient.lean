/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationValueBranches
/-! # A lower coefficient requests its actual inverse/raw product -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev ProductMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .coordinateGradientProduct q → matrixAxes P F q → answer q = productValue P F q

noncomputable def selected14Matrix (P : Parameters) (F : Family) (q : List Bool) : Bool :=
  selected P .eulerSum q && decide (matrixAxes P F q)

theorem selected14Matrix_FP (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : (fun q => [selected14Matrix P F q]) ∈ FP :=
  mem_FP_of_eq ((FPPred.of_flag (selected_FP P a .eulerSum)).and
    (((get_binary P a .row).lt (matrixDimension_binary P a F h)).and
      ((get_binary P a .col).lt (matrixDimension_binary P a F h)))).flag_mem_FP
    (fun q => by cases hb : selected P .eulerSum q <;> simp [selected14Matrix, matrixAxes, hb])

theorem selected14Matrix_iff (P : Parameters) (F : Family) (q : List Bool) : selected14Matrix P F q = true ↔
    (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 5 ∧ isPhase .eulerSum q) ∧ matrixAxes P F q := by
  simp only [selected14Matrix, Bool.and_eq_true, decide_eq_true_eq, selected_iff]

def lowerCoefficientProgram (P : Parameters) : SingleCall.Program where
  request _ := true
  query := IntegralCriticalFlatEulerBits.next P .coordinateGradientProduct
  immediate _ := []
  finish := pairSnd

theorem lowerCoefficient_controls (P : Parameters) (a : Access P) : (lowerCoefficientProgram P).Controls :=
  ⟨constFn_mem_FP [true], IntegralCriticalFlatEulerBits.next_FP P a .coordinateGradientProduct, constFn_mem_FP [], pairSnd_mem_FP⟩

noncomputable def lowerCoefficientStage (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (lowerCoefficientProgram P) ((lowerCoefficientProgram P).certificates (lowerCoefficient_controls P a))
    (selected14Matrix P F) (selected14Matrix_FP P a F h) (productValue P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem lowerCoefficient_correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (x : (q : List Bool) → ZMod (modulus P q))
    (hx : ProductMatches P F (fun q => residueBits (x q))) :
    Correct (lowerCoefficientStage P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have H := (selected14Matrix_iff P F q).mp hq
    have HE := (hx _ (next_valid P .coordinateGradientProduct q H.1.1)
      ((next_routine P .coordinateGradientProduct q).trans H.1.2.1)
      (IntegralCriticalFlatEulerBits.next_phase P .coordinateGradientProduct q)
      ((matrixAxes_next P F .coordinateGradientProduct q).mpr H.2)).trans
        (productValue_next P F .coordinateGradientProduct q)
    simpa only [SingleCall.Program.value, lowerCoefficientProgram, ite_true, pairSnd_pair] using HE
  · intro q _ _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (IntegralCriticalFlatEulerBits.next P .coordinateGradientProduct q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (IntegralCriticalFlatEulerBits.next_root P .coordinateGradientProduct q))
  · intro q c budget hq hc
    obtain ⟨_, rfl⟩ := ((lowerCoefficientProgram P).requests_iff _ budget q c).mp hc
    have HP := ((selected14Matrix_iff P F q).mp hq).1.2.2
    change phase q = 14 at HP
    exact next_frame P .coordinateGradientProduct q (by change 13 < phase q; omega)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
