/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextReductionEntry
public import LeanCanny.Algebra.IntegralMixedVirtualActionModel
/-! # Native virtual action entries request the actual preceding power -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open IntegralMixedVirtualUpperBits
set_option backward.isDefEq.respectTransparency false

theorem frame_of_tasks_same_routine (P : Parameters) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (ht : Tasks P q c) (hd : IntegralCriticalHistoryTask.rank P c < IntegralCriticalHistoryTask.rank P q) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  rcases ht with rfl | ht
  · exact False.elim (Nat.lt_irrefl _ hd)
  · exact IntegralMixedMatrixFrames.frame_of_ordinary P q c hr ⟨ht.1, ht.2, hd⟩

theorem frame19 (P : Parameters) (F : Family) (answer : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .actionEntry q)
    (hc : (IntegralCriticalFlatActionBits.program P (reduction P F)).controller.Requests answer budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  have HE := ((IntegralCriticalFlatActionBits.requests_iff P (reduction P F) answer budget q c).mp hc).2
  apply frame_of_tasks_same_routine P q c
  · rw [HE, IntegralMixedRoutineTaskBits.routine, IntegralCriticalFlatEulerBits.next_get]
    simp only [IntegralMixedRoutineTaskBits.routine]
  · exact IntegralCriticalFlatActionBits.requests_tasks P (reduction P F) answer budget q q c (tasks_self P q) hc
  · exact IntegralCriticalFlatActionBits.requests_rank P (reduction P F) answer budget q c hp hc

abbrev ActionRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  (IntegralCriticalFlatActionBits.program P (reduction P F)).request q = true →
    answer (IntegralCriticalFlatEulerBits.next P .reductionPower q) =
      powerValue P F (IntegralCriticalFlatEulerBits.next P .reductionPower q)

noncomputable def stage19 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  ofSingleCall (IntegralCriticalFlatActionBits.program P (reduction P F))
    ((IntegralCriticalFlatActionBits.program P (reduction P F)).certificates
      (IntegralCriticalFlatActionBits.controls P a (reduction P F) (reductionAccess P a F h) (reduction_controls P a F h)))
    (selectedFinite P .actionEntry (reductionSize P F))
    (selectedFinite_FP P a .actionEntry _ (reductionSize_binary P a F h))
    (IntegralMixedVirtualMatrixBits.actionEntry P F) (IntegralCriticalHistoryEvaluator.residueWidth P)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

theorem correct19 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hx : ∀ q, selectedFinite P .actionEntry (reductionSize P F) q = true → ActionRepliesAt P F (fun q => residueBits (x q)) q) :
    Correct (stage19 P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    have HSEL := (selectedFinite_iff P .actionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .actionEntry q HSEL.1
    exact value19 P F _ q (fun hr => (hx q hq (by simpa only [IntegralCriticalFlatActionBits.program, decide_eq_true_eq] using hr)).trans (power_next P F .reductionPower q)) ⟨_, HSEL.2.1⟩ ⟨_, HSEL.2.2⟩ rfl rfl
  · intro q hq hr
    have HSEL := (selectedFinite_iff P .actionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .actionEntry q HSEL.1
    let C := IntegralCriticalFlatActionBits.program P (reduction P F)
    have HC : C.controller.Requests (fun q => residueBits (x q)) (fun _ => 1) q (C.query q) :=
      (C.requests_iff _ _ _ _).mpr ⟨hr, rfl⟩
    have HF := frame19 P F _ (fun _ => 1) q (C.query q) H.2.2 HC
    have HE : IntegralCriticalHistoryEvaluator.residueWidth P (C.query q) = IntegralCriticalHistoryEvaluator.residueWidth P q :=
      congrArg (fun r => (numericCap P r).size) HF.1
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (C.query q)).trans_eq HE
  · intro q c budget hq hc
    have HSEL := (selectedFinite_iff P .actionEntry (reductionSize P F) q).mp hq
    have H := selected_base P .actionEntry q HSEL.1
    exact frame19 P F _ budget q c H.2.2 hc

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
