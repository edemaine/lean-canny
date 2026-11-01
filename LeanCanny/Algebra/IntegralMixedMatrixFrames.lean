/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineTask
/-! # Existing flat matrix writers decrease the mixed task rank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedMatrixFrames
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem lower_of_ordinary_rank (P : Parameters) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (h : IntegralCriticalHistoryTask.rank P c < IntegralCriticalHistoryTask.rank P q) :
    IntegralMixedRoutineTaskBits.rank P c < IntegralMixedRoutineTaskBits.rank P q := by
  have HC := IntegralMixedRoutineTaskBits.phase_lt c
  have HQ := IntegralMixedRoutineTaskBits.phase_lt q
  change 27 * birth P c + phase c < 27 * birth P q + phase q at h
  unfold IntegralMixedRoutineTaskBits.rank
  omega

theorem frame_of_ordinary (P : Parameters) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (h : RankedHistoryTask.root c = RankedHistoryTask.root q ∧ c.length ≤ wordBudget P q ∧
      IntegralCriticalHistoryTask.rank P c < IntegralCriticalHistoryTask.rank P q) :
    IntegralMixedRoutineTaskBits.Frame P q c :=
  ⟨h.1, h.2.1, lower_of_ordinary_rank P q c hr h.2.2⟩

theorem matrix_routine (P : Parameters) (p : Phase) (z : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (IntegralCriticalFlatMatrixQuery.writer P p z) =
      IntegralMixedRoutineTaskBits.routine P (pairFst z) := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatMatrixQuery.writer_get]
  rfl

theorem matrix_frame (P : Parameters) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (IntegralCriticalFlatMatrixQuery.writer P p z) :=
  frame_of_ordinary P _ _ (matrix_routine P p z)
    ⟨IntegralCriticalFlatMatrixQuery.writer_root P p z, IntegralCriticalFlatMatrixQuery.writer_length P p z,
      IntegralCriticalFlatMatrixQuery.writer_lower_rank P p z hp⟩

end LeanCanny.Algebra.IntegralMixedMatrixFrames
