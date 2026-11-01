/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpper
public import LeanCanny.Algebra.IntegralCriticalActualModel
/-! # The upper native dispatcher's canonical component model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem integerEntry_outside {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ)
    (h : ¬ (r < n ∧ t < n)) : IntegralCriticalTotalSnapshotBits.integerEntry M r t = 0 := by
  by_cases hr : r < n
  · have ht : ¬ t < n := fun ht => h ⟨hr, ht⟩
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_left hr, dite_eq_right ht]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_right hr]

theorem reduction_outside (F : Scripts) (q : List Bool) (h : ¬ finiteAxes F (reductionSize F) q) :
    IntegralCriticalFlatActualReductionEntryBits.value F q = [] := by
  unfold IntegralCriticalFlatActualReductionEntryBits.value IntegralCriticalTotalSnapshotBits.modularReductionEntry
    IntegralCriticalTotalSnapshotBits.reductionEntry
  rw [integerEntry_outside _ _ _ h]
  simp [residueBits, BinaryNatCode.encode]

theorem action_outside (F : Scripts) (q : List Bool) (h : ¬ finiteAxes F (reductionSize F) q) :
    IntegralCriticalFlatActualActionBits.value F q = [] := by
  unfold IntegralCriticalFlatActualActionBits.value IntegralCriticalTotalSnapshotBits.modularActionEntry
    IntegralCriticalTotalSnapshotBits.actionEntry
  rw [integerEntry_outside _ _ _ h]
  simp [residueBits, BinaryNatCode.encode]

theorem factor_outside (F : Scripts) (q : List Bool) (h : ¬ finiteAxes F (factorSize F) q) :
    IntegralCriticalFlatActualRelativeFactorBits.value F q = [] := by
  unfold IntegralCriticalFlatActualRelativeFactorBits.value IntegralCriticalTotalSnapshotBits.modularPowerEntry
    IntegralCriticalTotalSnapshotBits.powerEntry
  rw [integerEntry_outside _ _ _ h]
  simp [residueBits, BinaryNatCode.encode]

attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

theorem model_guard (F : Scripts) (h : Controls F) (q : List Bool) :
    model F h q = if IntegralCriticalTotalCompanionBits.valid F q then (inner F h).model q else [] := by
  change (if decide (IntegralCriticalTotalCompanionBits.valid F q) = true then (inner F h).model q else []) = _
  simp only [decide_eq_true_eq]

theorem model_invalid (F : Scripts) (h : Controls F) (q : List Bool)
    (hv : ¬ IntegralCriticalTotalCompanionBits.valid F q) : model F h q = [] := by
  rw [model_guard, ite_eq_right hv]

theorem stage17_model (F : Scripts) (h : Controls F) : (stage17 F h).model = IntegralCriticalFlatActualReductionEntryBits.value F := rfl
theorem stage17_selected (F : Scripts) (h : Controls F) : (stage17 F h).selected = selectedFinite F .reductionEntry (reductionSize F) := rfl

theorem stage18_model (F : Scripts) (h : Controls F) : (stage18 F h).model = IntegralCriticalTotalActionSnapshotBits.powerValue F := rfl
theorem stage18_selected (F : Scripts) (h : Controls F) : (stage18 F h).selected = selected F .reductionPower := rfl

theorem stage19_model (F : Scripts) (h : Controls F) : (stage19 F h).model = IntegralCriticalFlatActualActionBits.value F := rfl
theorem stage19_selected (F : Scripts) (h : Controls F) : (stage19 F h).selected = selectedFinite F .actionEntry (reductionSize F) := rfl

theorem stage21_model (F : Scripts) (h : Controls F) : (stage21 F h).model = IntegralCriticalFlatActualMomentBits.value F := rfl
theorem stage21_selected (F : Scripts) (h : Controls F) : (stage21 F h).selected = selected F .momentEntry := rfl

theorem stage22_model (F : Scripts) (h : Controls F) : (stage22 F h).model = IntegralCriticalTotalMomentValueSnapshotBits.value F := rfl
theorem stage22_selected (F : Scripts) (h : Controls F) : (stage22 F h).selected = selected F .momentPower := rfl

theorem stage23_model (F : Scripts) (h : Controls F) : (stage23 F h).model = IntegralCriticalFlatActualRelativeFactorBits.value F := rfl
theorem stage23_selected (F : Scripts) (h : Controls F) : (stage23 F h).selected = selectedFinite F .relativeFactor (factorSize F) := rfl

theorem stage24_model (F : Scripts) (h : Controls F) : (stage24 F h).model = (characteristic F).value := rfl
theorem stage24_selected (F : Scripts) (h : Controls F) : (stage24 F h).selected = selected F .relativePower := rfl

theorem stage25_model (F : Scripts) (h : Controls F) : (stage25 F h).model = IntegralCriticalTotalCreatingBits.coefficientValue F := rfl
theorem stage25_selected (F : Scripts) (h : Controls F) : (stage25 F h).selected = selected F .criticalCoefficient := rfl

theorem stage26_model (F : Scripts) (h : Controls F) : (stage26 F h).model = IntegralCriticalFlatHeightBits.companionValue F := rfl
theorem stage26_selected (F : Scripts) (h : Controls F) : (stage26 F h).selected = selected F .companion := rfl

attribute [local irreducible] IntegralCriticalFlatActualReductionEntryBits.value IntegralCriticalFlatActualActionBits.value
  IntegralCriticalFlatActualRelativeFactorBits.value
attribute [local irreducible] stage17 stage18 stage19 stage21 stage22 stage23 stage24 stage25 stage26

theorem inner_model (F : Scripts) (h : Controls F) (q : List Bool) : (inner F h).model q =
    bif selectedFinite F .reductionEntry (reductionSize F) q then IntegralCriticalFlatActualReductionEntryBits.value F q else
    bif selected F .reductionPower q then IntegralCriticalTotalActionSnapshotBits.powerValue F q else
    bif selectedFinite F .actionEntry (reductionSize F) q then IntegralCriticalFlatActualActionBits.value F q else
    bif selected F .momentEntry q then IntegralCriticalFlatActualMomentBits.value F q else
    bif selected F .momentPower q then IntegralCriticalTotalMomentValueSnapshotBits.value F q else
    bif selectedFinite F .relativeFactor (factorSize F) q then IntegralCriticalFlatActualRelativeFactorBits.value F q else
    bif selected F .relativePower q then (characteristic F).value q else
    bif selected F .criticalCoefficient q then IntegralCriticalTotalCreatingBits.coefficientValue F q else
    bif selected F .companion q then IntegralCriticalFlatHeightBits.companionValue F q else [] := by
  simp only [inner, choose_model, stage17_model, stage17_selected, stage18_model, stage18_selected, stage19_model, stage19_selected, stage21_model, stage21_selected, stage22_model, stage22_selected, stage23_model, stage23_selected, stage24_model, stage24_selected, stage25_model, stage25_selected, stage26_model, stage26_selected]
  simp only [zero, ofSingleCall]

theorem model_phase (F : Scripts) (h : Controls F) (p : Phase) (q : List Bool)
    (hp : 17 ≤ p.code) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hq : isPhase p q) :
    model F h q = IntegralCriticalActualModelBits.component F p q := by
  rw [model_guard, ite_eq_left hv, inner_model]
  cases p <;> simp only [Phase.code] at hp
  all_goals try omega
  all_goals simp only [isPhase, Phase.code] at hq
  all_goals simp only [selectedFinite, selected, hv, true_and, false_and, isPhase, hq, Phase.code,
    Nat.reduceEqDiff, Bool.cond_eq_ite, decide_eq_true_eq, decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true,
    IntegralCriticalActualModelBits.component]
  · split
    · rfl
    · exact (reduction_outside F q (by assumption)).symm
  · split
    · rfl
    · exact (action_outside F q (by assumption)).symm
  · split
    · rfl
    · exact (factor_outside F q (by assumption)).symm

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits
