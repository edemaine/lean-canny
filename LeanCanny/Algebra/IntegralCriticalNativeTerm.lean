/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native guarded original-grid term branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.euler F
noncomputable abbrev program (F : Scripts) := IntegralCriticalFlatGenericGridBits.termProgram F.toParameters (source F)
abbrev input (F : Scripts) := IntegralCriticalFlatGridBits.termInput F.toParameters

theorem certificates (F : Scripts) (h : Controls F) :
    (program F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F).certificates (IntegralCriticalFlatGenericGridBits.term_controls F.toParameters h.task.toAccess (source F) (eulerAccess F h))

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofPreparedSingleCall (program F) (certificates F h) (input F) (IntegralCriticalFlatGridBits.termInput_FP F.toParameters h.task.toAccess)
    (selected F .originalGridTerm) (selected_FP F h .originalGridTerm) (IntegralCriticalActualGridTransport.term F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .originalGridTerm q) (hc : ((program F).controller.prepare (input F)).Requests reply budget q c) : Frame F q c := by
  have HC0 := (RecursiveController.Controller.prepare_requests_iff (program F).controller (input F) reply budget q c).mp hc
  obtain ⟨_, rfl⟩ := ((program F).requests_iff reply (fun _ => budget q) (input F q) c).mp HC0
  have HQ : (program F).query (input F q) = IntegralCriticalFlatGridBits.writer F.toParameters .productPower (input F q) := rfl
  rw [HQ]
  have HP : 6 < phase (pairFst (input F q)) := by
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    change phase q = 7 at hp
    omega
  simpa only [IntegralCriticalFlatGridBits.termInput_parent] using frame_grid F .productPower (input F q) HP

theorem value_at (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) (input F q) = IntegralCriticalActualGridTransport.term F q := by
  apply Eq.trans (single_value_congr_at (program F) (answer F x) (IntegralCriticalActualGridTransport.product F) (input F q) ?_)
    (IntegralCriticalActualGridTransport.term_value F q)
  intro _
  exact matches_grid F x hm .productPower (by decide) (input F q) (by
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    exact hv)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply prepared_correct_of_frame F h .originalGridTerm (program F) (certificates F h) (input F)
    (IntegralCriticalFlatGridBits.termInput_FP F.toParameters h.task.toAccess) (IntegralCriticalActualGridTransport.term F) x
  · intro q hq
    exact value_at F x hm q ((selected_iff F .originalGridTerm q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F (answer F x) budget q c ((selected_iff F .originalGridTerm q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeTermBits
