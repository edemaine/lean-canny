/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousBranch

/-! # Deleting the second formal digit requests the same homogeneous source

Routine two, phase 23, divides each second-prefix basis index by the one
fixed nilpotent degree and requests phase 22. The source, system row,
monomial, selected original row and caller modulus are retained literally.
The quotients fit the task cap because they never exceed their incoming
bounded fields; no new degree or matrix bound is supplied by a caller.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable abbrev parameters (P : Parameters) (F : Family) :=
  IntegralMixedValueSystemControls.parameters (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)

theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    IntegralReciprocalEntryRequest.Controls (parameters P F) :=
  IntegralMixedValueSystemControls.controls _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)

noncomputable def oldRow (P : Parameters) (F : Family) (q : List Bool) := get P .row q / (parameters P F).digit q
noncomputable def oldCol (P : Parameters) (F : Family) (q : List Bool) := get P .col q / (parameters P F).digit q

theorem oldRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (oldRow P F) :=
  (get_binary P a .row).div (controls P a F h).digit
theorem oldCol_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (oldCol P F) :=
  (get_binary P a .col).div (controls P a F h).digit

noncomputable def rowTask (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscEntry .momentPower .row (oldRow P F)
noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (rowTask P F) .pscEntry .momentPower .col (oldCol P F)

theorem rowTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : rowTask P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (oldRow_binary P a F h)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (rowTask_FP P a F h) _ _ _ _ (oldCol_binary P a F h)

theorem oldRow_cap (P : Parameters) (F : Family) (q : List Bool) :
    oldRow P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.div_le_self _ _).trans (get_le P .row q)
theorem oldCol_cap (P : Parameters) (F : Family) (q : List Bool) :
    oldCol P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.div_le_self _ _).trans (get_le P .col q)

theorem rowTask_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (rowTask P F q) = RankedHistoryTask.root q :=
  IntegralMixedValueFieldQuery.query_root P id _ _ _ _ q

theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P (rowTask P F) _ _ _ _ q).trans (rowTask_root P F q)

theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P (rowTask P F) _ _ _ _ q).trans
    (IntegralMixedValueFieldQuery.query_birth P id _ _ _ _ q)

theorem query_get (P : Parameters) (F : Family) (q : List Bool) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 2 else if f = .col then oldCol P F q else
      if f = .row then oldRow P F q else get P f q := by
  rw [query, IntegralMixedValueFieldQuery.query_get, rowTask_root]
  rw [rowTask, IntegralMixedValueFieldQuery.query_get]
  simp only [id_eq, min_eq_left (oldRow_cap P F q), min_eq_left (oldCol_cap P F q)]
  cases f <;> rfl

theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact query_root P F q
  · exact query_birth P F q
  · simp only [query_get, reduceCtorEq, ite_false]

theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q := by
  unfold modulus
  simp only [query_get, reduceCtorEq, ite_false]

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 23) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have HL := IntegralMixedValueFieldQuery.query_length P (rowTask P F) .pscEntry .momentPower .col (oldCol P F) q
    have HW : wordBudget P (rowTask P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [rowTask_root]
    exact HL.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (query_birth P F q)
    · rw [IntegralMixedRoutineTaskBits.routine, query_get, hr]
      simp only [reduceCtorEq, ite_true]
      decide
    · rw [query, IntegralMixedValueFieldQuery.query_phase, hp]
      decide

end LeanCanny.Algebra.IntegralMixedValueReciprocalTasks
