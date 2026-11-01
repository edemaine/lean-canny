/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindValueSelection
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientClosure
/-! # Restoring immutable cut payloads preserves the native raw task frame -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem coordinate_choice_lt (F : Family) (key : List Bool) (ht : tag F key = 2) :
    choice F key < IntegralMixedCoordinateTrailing.ChoiceBound (F.spatial key) (F.rule key) := by
  cases hk : F.kind key with
  | coordinate j c => simpa only [choice, hk] using c.isLt
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c => simp only [tag, hk] at ht; omega

theorem value_choice_lt (F : Family) (key : List Bool) (ht : tag F key = 4) :
    choice F key < IntegralMixedValueTrailing.ChoiceBound (F.spatial key) (F.rule key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c => simpa only [choice, hk] using c.isLt

theorem prepare_context (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedVirtualContextBits.context P (prepare P F q) ↔ IntegralMixedVirtualContextBits.context P q := by
  simp only [IntegralMixedVirtualContextBits.context, prepare_get P F g q, reduceCtorEq, ite_false]

theorem prepare_valid (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualCaps.valid P (prepare P F q) ↔ IntegralMixedVirtualCaps.valid P q := by
  unfold IntegralMixedVirtualCaps.valid
  rw [prepare_root, prepare_birth]

theorem prepare_labels (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedValueCoefficientTasks.Labels P F (prepare P F q) ↔ IntegralMixedValueCoefficientTasks.Labels P F q := by
  simp only [IntegralMixedValueCoefficientTasks.Labels, IntegralMixedValueCoefficientTasks.oldRank,
    IntegralMixedValueCoefficientTasks.scalar, prepare_saved, prepare_get P F g q, reduceCtorEq, ite_false]

theorem prepare_frame (P : Parameters) (F : Family) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 4) (hp : phase q = 26)
    (hc : IntegralMixedRoutineTaskBits.Frame P (prepare P F q) c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  refine ⟨hc.1.trans (prepare_root P F q), ?_, ?_⟩
  · have hw : wordBudget P (prepare P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [prepare_root]
    exact hc.2.1.trans_eq hw
  · have he : IntegralMixedRoutineTaskBits.rank P (prepare P F q) = IntegralMixedRoutineTaskBits.rank P q := by
      unfold IntegralMixedRoutineTaskBits.rank
      rw [prepare_birth, prepare_routine, prepare_phase, hr, hp]
    exact hc.2.2.trans_eq he

end LeanCanny.Algebra.IntegralMixedRawKindBits
