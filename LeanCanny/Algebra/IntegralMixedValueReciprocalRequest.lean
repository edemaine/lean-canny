/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousSnapshot

/-! # Native second-digit selection with the actual homogeneous child

The guarded request asks phase 22 at the quotient basis indices. The
immediate branch is the literal negative chart identity or zero. Every
local operation has native FP certificates; the only semantic reply is
the current homogeneous matrix entry at that emitted smaller task.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueReciprocalRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueReciprocalTasks
open scoped Classical

noncomputable def request (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralReciprocalEntryRequest.request (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q)
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (request P F q) :=
  inferInstanceAs (Decidable (IntegralReciprocalEntryRequest.request _ _))

noncomputable def immediate (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralReciprocalEntryRequest.immediate (parameters P F) (IntegralMixedValueHomogeneousQueries.packet P q)

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request q := decide (request P F q)
  query := query P F
  immediate := immediate P F
  finish := pairSnd

theorem request_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (request P F) :=
  (IntegralReciprocalEntryRequest.request_FP _ (controls P a F h)).comp (IntegralMixedValueHomogeneousQueries.packet_FP P a)
theorem immediate_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : immediate P F ∈ FP :=
  mem_FP_comp (IntegralMixedValueHomogeneousQueries.packet_FP P a) (IntegralReciprocalEntryRequest.immediate_FP _ (controls P a F h))
theorem program_controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨(request_FP P a F h).flag_mem_FP, query_FP P a F h, immediate_FP P a F h, pairSnd_mem_FP⟩
theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program P F).certificates (program_controls P a F h)

theorem packet_value (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) :
    (program P F).value reply q =
      (IntegralMixedValueSystemControls.program (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F)).value (fun _ => reply (query P F q))
          (IntegralMixedValueHomogeneousQueries.packet P q) := by
  by_cases HR : request P F q <;>
    simp_all only [SingleCall.Program.value, program, IntegralMixedValueSystemControls.program,
      IntegralReciprocalEntryRequest.program, request, immediate, pairSnd_pair, decide_eq_true_eq, ite_true, ite_false]

theorem value_eq (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) :
    (program P F).value reply q = if request P F q then reply (query P F q) else immediate P F q := by
  simp only [SingleCall.Program.value, program, decide_eq_true_eq, pairSnd_pair]

theorem requests_iff (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) : (program P F).controller.Requests reply budget q c ↔ request P F q ∧ c = query P F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_frame (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 23)
    (hc : (program P F).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  rw [((requests_iff P F reply budget q c).mp hc).2]
  exact query_frame P F q hr hp

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  request P F q → reply (query P F q) = IntegralMixedValueHomogeneousMatrix.value P F (query P F q)

theorem state_length (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (he : RepliesAt P F reply q) :
    (SingleCall.encState (((program P F).controller.reference reply)^[t] (SingleCall.Program.initial q))).length ≤
      IntegralMixedValueHomogeneousRequest.stateBound P q := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  apply (program P F).state_length_of_bound reply q t ((modulus P q).size)
  intro HR
  have HQ : request P F q := of_decide_eq_true HR
  change (reply (query P F q)).length ≤ _
  rw [he HQ, IntegralMixedValueHomogeneousSnapshot.reciprocal_child]
  exact residueBits_length_le _ _

end LeanCanny.Algebra.IntegralMixedValueReciprocalRequest
