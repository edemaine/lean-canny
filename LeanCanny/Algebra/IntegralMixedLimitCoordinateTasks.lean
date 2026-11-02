/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientClosure

/-! # Shifted critical coefficient requests for a limit-coordinate cut

The original slot8 is the E coefficient c; the original coefficient field
is the requested coordinate degree k. Local preparation requests T^k E^(c-k)
from the existing critical routine. The preparation is not a recursive call.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits

def first (P : Parameters) := IntegralMixedValueFieldQuery.query P id .rawFactor .companion
  .coefficient (fun q => get P .slot8 q - get P .coefficient q)
def prepare (P : Parameters) := IntegralMixedValueFieldQuery.query P (first P) .rawFactor .companion
  .slot8 (get P .coefficient)

theorem first_FP (P : Parameters) (a : Access P) : first P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _
    ((get_binary P a .slot8).sub (get_binary P a .coefficient))
theorem prepare_FP (P : Parameters) (a : Access P) : prepare P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a) _ _ _ _ (get_binary P a .coefficient)

theorem prepare_root (P : Parameters) (q : List Bool) :
    RankedHistoryTask.root (prepare P q) = RankedHistoryTask.root q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem prepare_birth (P : Parameters) (q : List Bool) : birth P (prepare P q) = birth P q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem prepare_saved (P : Parameters) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (prepare P q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P id _ _ _ _ q (by decide))
theorem prepare_modulus (P : Parameters) (q : List Bool) : modulus P (prepare P q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P _ _ _ _ _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_modulus P id _ _ _ _ q (by decide))
theorem prepare_routine (P : Parameters) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (prepare P q) = 4 :=
  IntegralMixedValueFieldQuery.query_routine P _ _ _ _ _ q
theorem prepare_phase (P : Parameters) (q : List Bool) : phase (prepare P q) = 26 :=
  IntegralMixedValueFieldQuery.query_phase P _ _ _ _ _ q

theorem prepare_get (P : Parameters) (q : List Bool) (f : Field) :
    get P f (prepare P q) = if f = .slot14 then 4 else
      if f = .slot8 then get P .coefficient q else
      if f = .coefficient then get P .slot8 q - get P .coefficient q else get P f q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_get,
    IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (get_le P .coefficient q),
    min_eq_left ((Nat.sub_le (get P .slot8 q) (get P .coefficient q)).trans (get_le P .slot8 q))]
  cases f <;> rfl

theorem prepare_valid (P : Parameters) (q : List Bool) :
    IntegralMixedVirtualCaps.valid P (prepare P q) ↔ IntegralMixedVirtualCaps.valid P q := by
  unfold IntegralMixedVirtualCaps.valid
  rw [prepare_root, prepare_birth]

noncomputable def critical (P : Parameters) (F : Family) :=
  IntegralMixedCoordinateCoefficientTasks.query P F ∘ prepare P

theorem critical_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : critical P F ∈ FP :=
  mem_FP_comp (prepare_FP P a) (IntegralMixedCoordinateCoefficientTasks.query_FP P a F h)
theorem critical_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (critical P F q) = RankedHistoryTask.root q :=
  (IntegralMixedCoordinateCoefficientTasks.query_root P F _).trans (prepare_root P q)
theorem critical_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (critical P F q) = birth P q :=
  (IntegralMixedCoordinateCoefficientTasks.query_birth P F _).trans (prepare_birth P q)
theorem critical_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (critical P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedCoordinateCoefficientTasks.query_saved P F _).trans (prepare_saved P q)
theorem critical_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (critical P F q) = modulus P q :=
  (IntegralMixedCoordinateCoefficientTasks.query_modulus P F _).trans (prepare_modulus P q)
theorem critical_routine (P : Parameters) (F : Family) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (critical P F q) = 1 :=
  IntegralMixedCoordinateCoefficientTasks.query_routine P F _
theorem critical_phase (P : Parameters) (F : Family) (q : List Bool) : phase (critical P F q) = 25 :=
  IntegralMixedCoordinateCoefficientTasks.query_phase P F _

theorem critical_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 4) : IntegralMixedRoutineTaskBits.Frame P q (critical P F q) := by
  have H := IntegralMixedCoordinateCoefficientTasks.query_frame P F (prepare P q) (prepare_routine P q)
  refine ⟨critical_root P F q, ?_, ?_⟩
  · have HW : wordBudget P (prepare P q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [prepare_root]
    exact H.2.1.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (critical_birth P F q)
    rw [critical_routine, hr]
    decide

end LeanCanny.Algebra.IntegralMixedLimitCoordinateTasks
