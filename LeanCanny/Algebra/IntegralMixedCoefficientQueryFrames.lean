/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoefficientQuery
/-! # Same-routine coefficient requests decrease their native phase -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoefficientQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedRoutineTaskBits (Routine)
set_option backward.isDefEq.respectTransparency false

theorem writer_length (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    (writer P r p z).length ≤ wordBudget P (pairFst z) :=
  child_length P pairFst (birth P ∘ pairFst) p (reader P r) z (min_le_right _ _)

theorem writer_frame_phase (P : Parameters) (r : Routine) (p : Phase) (z : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = r.code) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (writer P r p z) := by
  refine ⟨writer_root P r p z, writer_length P r p z, ?_⟩
  apply IntegralMixedRoutineTaskBits.lower_phase P (pairFst z) _ (writer_birth P r p z)
  · rw [writer_routine]
    exact hr.symm
  · rw [writer_phase]
    exact hp

end LeanCanny.Algebra.IntegralMixedCoefficientQueryBits
