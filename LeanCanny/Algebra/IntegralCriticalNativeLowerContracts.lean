/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativePreparedSingleCallBranch
public import LeanCanny.Algebra.IntegralCriticalNativeLowerFrames
/-! # Selected single-call contracts from actual critical-task frames -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem single_value_congr_at (P : SingleCall.Program) (a b : List Bool → List Bool) (q : List Bool)
    (h : P.request q = true → a (P.query q) = b (P.query q)) : P.value a q = P.value b q := by
  unfold SingleCall.Program.value
  cases hr : P.request q with
  | false => rfl
  | true => simp only [ite_true]; rw [h hr]

theorem single_correct_of_frame (F : Scripts) (h : Controls F) (p : Phase) (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState))
    (value : List Bool → List Bool) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hv : ∀ q, selected F p q = true → P.value (answer F x) q = value q)
    (hf : ∀ q c budget, selected F p q = true → P.controller.Requests (answer F x) budget q c → Frame F q c) :
    Correct (ofSingleCall P hP (selected F p) (selected_FP F h p) value
      (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
      (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)) (answer F x) (Frame F) := by
  apply ofSingleCall_correct
  · exact hv
  · intro q hq hr
    have HC := (P.requests_iff (answer F x) (fun _ => 1) q (P.query q)).mpr ⟨hr, rfl⟩
    exact IntegralCriticalNativeBranchBits.answer_length F x q _ (hf q _ (fun _ => 1) hq HC).1
  · exact hf

theorem prepared_correct_of_frame (F : Scripts) (h : Controls F) (p : Phase) (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState))
    (input : List Bool → List Bool) (hi : input ∈ FP) (value : List Bool → List Bool)
    (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hv : ∀ q, selected F p q = true → P.value (answer F x) (input q) = value q)
    (hf : ∀ q c budget, selected F p q = true → (P.controller.prepare input).Requests (answer F x) budget q c → Frame F q c) :
    Correct (ofPreparedSingleCall P hP input hi (selected F p) (selected_FP F h p) value
      (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
      (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)) (answer F x) (Frame F) := by
  apply ofPreparedSingleCall_correct
  · exact hv
  · intro q hq hr
    have HC : (P.controller.prepare input).Requests (answer F x) (fun _ => 1) q (P.query (input q)) :=
      (RecursiveController.Controller.prepare_requests_iff P.controller input (answer F x) (fun _ => 1) q _).mpr
        ((P.requests_iff (answer F x) (fun _ => 1) (input q) _).mpr ⟨hr, rfl⟩)
    exact IntegralCriticalNativeBranchBits.answer_length F x q _ (hf q _ (fun _ => 1) hq HC).1
  · exact hf


theorem fold_requests_bound (P : RecursiveFold.Program) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hc : P.controller.Requests reply budget q c) : P.controller.Requests reply P.count q c := by
  obtain ⟨t, _, hh, _, he⟩ := hc
  have HI : min t (P.count q) < P.count q := by
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at hh
    have H : ¬ P.count q ≤ min t (P.count q) := of_decide_eq_false hh
    omega
  apply (P.requests_iff reply q c).mpr
  refine ⟨min t (P.count q), HI, ?_⟩
  rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at he
  exact he

end LeanCanny.Algebra.IntegralCriticalNativeLowerBits
