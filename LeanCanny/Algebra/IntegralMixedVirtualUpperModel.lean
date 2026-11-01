/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualUpperOutside
/-! # The upper arithmetic dispatcher returns its literal virtual component -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualUpperBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

theorem stage17_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage17 P a F h).model = IntegralMixedVirtualMatrixBits.reductionEntry P F := rfl
theorem stage17_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage17 P a F h).selected = selectedFinite P .reductionEntry (reductionSize P F) := rfl
theorem stage18_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage18 P a F h).model = powerValue P F := rfl
theorem stage18_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage18 P a F h).selected = selected P .reductionPower := rfl
theorem stage19_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage19 P a F h).model = IntegralMixedVirtualMatrixBits.actionEntry P F := rfl
theorem stage19_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage19 P a F h).selected = selectedFinite P .actionEntry (reductionSize P F) := rfl
theorem stage21_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage21 P a F h).model = momentEntry P F := rfl
theorem stage21_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage21 P a F h).selected = selected P .momentEntry := rfl
theorem stage22_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage22 P a F h).model = momentValue P F := rfl
theorem stage22_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage22 P a F h).selected = selected P .momentPower := rfl
theorem stage23_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage23 P a F h).model = IntegralMixedVirtualMatrixBits.relativeFactor P F := rfl
theorem stage23_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage23 P a F h).selected = selectedFinite P .relativeFactor (factorSize P F) := rfl
theorem stage24_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage24 P a F h).model = (characteristic P F).value := rfl
theorem stage24_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage24 P a F h).selected = selected P .relativePower := rfl
theorem stage25_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage25 P a F h).model = (critical P F).value := rfl
theorem stage25_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (stage25 P a F h).selected = selected P .criticalCoefficient := rfl

attribute [local irreducible] stage17 stage18 stage19 stage21 stage22 stage23 stage24 stage25

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) (q : List Bool) :
    (machine P a F h).model q =
      bif selectedFinite P .reductionEntry (reductionSize P F) q then IntegralMixedVirtualMatrixBits.reductionEntry P F q else
      bif selected P .reductionPower q then powerValue P F q else
      bif selectedFinite P .actionEntry (reductionSize P F) q then IntegralMixedVirtualMatrixBits.actionEntry P F q else
      bif selected P .momentEntry q then momentEntry P F q else
      bif selected P .momentPower q then momentValue P F q else
      bif selectedFinite P .relativeFactor (factorSize P F) q then IntegralMixedVirtualMatrixBits.relativeFactor P F q else
      bif selected P .relativePower q then (characteristic P F).value q else
      bif selected P .criticalCoefficient q then (critical P F).value q else
      [] := by
  simp only [machine, choose_model, stage17_model, stage17_selected, stage18_model, stage18_selected, stage19_model, stage19_selected, stage21_model, stage21_selected, stage22_model, stage22_selected, stage23_model, stage23_selected, stage24_model, stage24_selected, stage25_model, stage25_selected]
  rfl

noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .reductionEntry => IntegralMixedVirtualMatrixBits.reductionEntry P F
  | .reductionPower => powerValue P F
  | .actionEntry => IntegralMixedVirtualMatrixBits.actionEntry P F
  | .momentEntry => momentEntry P F
  | .momentPower => momentValue P F
  | .relativeFactor => IntegralMixedVirtualMatrixBits.relativeFactor P F
  | .relativePower => (characteristic P F).value
  | .criticalCoefficient => (critical P F).value
  | _ => fun _ => []

attribute [local irreducible] IntegralMixedVirtualMatrixBits.reductionEntry IntegralMixedVirtualMatrixBits.actionEntry
  IntegralMixedVirtualMatrixBits.relativeFactor momentEntry momentValue powerValue characteristic
  IntegralClearedCriticalBits.Source.value IntegralBerkowitzBlockBits.Source.value

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (p : Phase) (q : List Bool) (hp17 : 17 ≤ p.code) (hp25 : p.code ≤ 25) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hp : isPhase p q) :
    (machine P a F h).model q = component P F p q := by
  rw [machine_model]
  cases p <;> simp only [Phase.code] at hp17 hp25
  all_goals try omega
  all_goals simp only [isPhase, Phase.code] at hp
  all_goals simp only [selectedFinite, selected, hv, hr, true_and, isPhase, hp, Phase.code,
    Nat.reduceEqDiff, Bool.false_and, Bool.true_and, Bool.cond_eq_ite, decide_eq_true_eq, decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true, component]
  · split
    · rfl
    · exact (reduction_outside P F q (by simp_all only [decide_eq_true_eq, not_false_eq_true])).symm
  · split
    · rfl
    · exact (action_outside P F q (by simp_all only [decide_eq_true_eq, not_false_eq_true])).symm
  · split
    · rfl
    · exact (factor_outside P F q (by simp_all only [decide_eq_true_eq, not_false_eq_true])).symm

end LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits
