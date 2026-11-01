/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowTasks
public import LeanCanny.Algebra.IntegralMixedFullRowRequest

/-! # Native full original-row assembly at routine two, phase 21

Actual lower and scalar tasks are fixed by the source and row kind. Two
current residue replies restore the literal original-row matrix entry;
all local arithmetic and query writers are native FP. Current-reply
equalities are the semantic induction hypotheses of the dispatcher, not
additional coefficient, scalar or matrix computation premises.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedFullRowTasks
open scoped Classical

noncomputable def program (P : Parameters) (F : Family) :=
  IntegralMixedFullRowRequest.program (family P F) (indices P F) (width P F) (lowTask P F) (scalarTask P F)

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralMixedFullRowRequest.certificates _ _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)
    (width_unary P a F h) _ _ (lowTask_FP P a F h) (scalarTask_FP P a F h)

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (lowTask P F q) = IntegralMixedFullRowRequest.lowValue (family P F) (indices P F) (width P F) q ∧
  reply (scalarTask P F q) = residueBits (IntegralMixedFullRowMultiplier.scalar (family P F) (indices P F) q : ZMod (modulus P q))

theorem value_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (hr : RepliesAt P F reply q) :
    (program P F).value reply q = IntegralMixedValueRestoredSource.value P F q :=
  (IntegralMixedFullRowRequest.value_at _ _ _ _ _ reply q hr.1 hr.2).trans
    (IntegralMixedValueRestoredSource.value_full_row P F q).symm

theorem stateBound_unary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    UnaryFn (IntegralMixedFullRowRequest.stateBound (family P F) (indices P F)) :=
  IntegralMixedFullRowRequest.stateBound_unary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)

theorem state_length (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (hr : RepliesAt P F reply q) (t : ℕ) :
    (RecursiveFold.encState (((program P F).controller.reference reply)^[t] ((program P F).initial q))).length ≤
      IntegralMixedFullRowRequest.stateBound (family P F) (indices P F) q :=
  IntegralMixedFullRowRequest.state_length _ _ _ _ _ reply q hr.1 hr.2 t

theorem task_frame (P : Parameters) (F : Family) (p : Phase) (x : ℕ) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) :
    IntegralMixedRoutineTaskBits.Frame P q (taskAt P F p x q) := by
  refine ⟨task_root P F p x q, ?_, ?_⟩
  · have HL := IntegralMixedValueFieldQuery.query_length P (targetTask P F p) .critical p .expression (fun _ => x) q
    have HW : wordBudget P (targetTask P F p q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [target_root]
    exact HL.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (task_birth P F p x q)
    rw [IntegralMixedRoutineTaskBits.routine, task_get, hr]
    simp only [reduceCtorEq, ite_true]
    decide

theorem lowTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) :
    IntegralMixedRoutineTaskBits.Frame P q (lowTask P F q) := by
  unfold lowTask
  split_ifs <;> exact task_frame P F _ _ q hr

theorem scalarTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) :
    IntegralMixedRoutineTaskBits.Frame P q (scalarTask P F q) := by
  unfold scalarTask
  split_ifs
  · exact IntegralMixedRoutineTaskBits.query_frame_routine P .scalar .productEntry q (by rw [hr]; decide)
  · exact IntegralMixedScalarQueryBits.scalar_frame P .monomialFactor q (by rw [hr]; decide)

theorem requests_frame (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2)
    (hc : (program P F).controller.Requests reply (fun _ => 2) q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  rcases (IntegralMixedFullRowRequest.requests_iff _ _ _ _ _ reply q c).mp hc with rfl | rfl
  · exact lowTask_frame P F q hr
  · exact scalarTask_frame P F q hr

end LeanCanny.Algebra.IntegralMixedFullRowNative
