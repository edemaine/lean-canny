/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeBranch
public import LeanCanny.Algebra.IntegralCriticalTotalHeight
/-! # Phase two is one native branch calling only earlier companions -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofSingleCall (IntegralCriticalTotalHeightBits.program F)
    ((IntegralCriticalTotalHeightBits.program F).certificates
      (IntegralCriticalTotalHeightBits.program_controls F h.task h.metadata))
    (selected F .clearedHeight) (selected_FP F h .clearedHeight) (IntegralCriticalTotalHeightBits.value F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (IntegralCriticalTotalHeightBits.program F).controller.Requests reply budget q c) : Frame F q c := by
  refine ⟨?_, IntegralCriticalTotalHeightBits.requests_length F reply budget q c hc,
    IntegralCriticalTotalHeightBits.requests_rank F reply budget q c hc⟩
  obtain ⟨_, rfl⟩ := (IntegralCriticalFlatClearedHeightBits.requests_iff F reply budget q c).mp hc
  exact IntegralCriticalFlatClearedHeightBits.earlierChild_root F q

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (h26 : ∀ q, IntegralCriticalTotalCompanionBits.valid F q → isPhase .companion q →
      answer F x q = IntegralCriticalFlatHeightBits.companionValue F q) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply ofSingleCall_correct
  · intro q _
    apply IntegralCriticalTotalHeightBits.program_value_local
    intro hr
    let c := IntegralCriticalFlatClearedHeightBits.earlierChild F q
    have HC : (IntegralCriticalTotalHeightBits.program F).controller.Requests (answer F x) (fun _ => 1) q c :=
      (IntegralCriticalFlatClearedHeightBits.requests_iff F _ _ q c).mpr ⟨hr, rfl⟩
    exact h26 c (IntegralCriticalTotalHeightBits.requests_valid F _ _ q c HC)
      (IntegralCriticalTotalHeightBits.requests_phase F _ _ q c HC)
  · intro q _ hr
    have HC := ((IntegralCriticalTotalHeightBits.program F).requests_iff (answer F x) (fun _ => 1) q
      ((IntegralCriticalTotalHeightBits.program F).query q)).mpr ⟨hr, rfl⟩
    exact IntegralCriticalNativeBranchBits.answer_length F x q _ (requests_frame F _ _ q _ HC).1
  · intro q c budget _ hc
    exact requests_frame F _ budget q c hc

end LeanCanny.Algebra.IntegralCriticalNativeHeightBits
