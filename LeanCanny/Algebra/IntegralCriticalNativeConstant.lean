/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native actual frozen constant branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeConstantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.FrozenStages.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalTotalCreatingBits.FrozenStages.access F h
noncomputable abbrev program (F : Scripts) (h : Controls F) := IntegralCriticalFlatFrozenConstantBits.program F.toParameters (source F) (access F h)

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofSingleCall (program F h) (IntegralCriticalTotalCreatingBits.FrozenStages.constant_certificates F h)
    (selected F .frozenConstant) (selected_FP F h .frozenConstant) (IntegralCriticalActualScalarModels.frozenConstant F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem requests_frame (F : Scripts) (h : Controls F) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .frozenConstant q) (hc : (program F h).controller.Requests reply budget q c) : Frame F q c := by
  obtain ⟨_, rfl⟩ := ((program F h).requests_iff reply budget q c).mp hc
  have HQ : (program F h).query q = IntegralCriticalFlatEulerBits.next F.toParameters .frozenPowerSum q := rfl
  rw [HQ]
  apply frame_next
  change phase q = 11 at hp
  change 10 < phase q
  omega

theorem value_at (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F h).value (answer F x) q = IntegralCriticalActualScalarModels.frozenConstant F q := by
  have HC := single_value_congr_at (program F h) (answer F x) (IntegralCriticalActualScalarModels.frozenSum F) q
    (fun _ => matches_next F x hm .frozenPowerSum (by decide) q hv)
  exact HC.trans ((IntegralCriticalFlatFrozenConstantBits.value_local F.toParameters (source F) (access F h)
    (IntegralCriticalActualScalarModels.frozenSum F) q (IntegralCriticalActualFrozenTransport.constant_replies F q)).trans
      (IntegralCriticalActualScalarModels.frozenConstant_eq F q).symm)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply single_correct_of_frame F h .frozenConstant (program F h)
    (IntegralCriticalTotalCreatingBits.FrozenStages.constant_certificates F h) (IntegralCriticalActualScalarModels.frozenConstant F) x
  · intro q hq
    exact value_at F h x hm q ((selected_iff F .frozenConstant q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F h (answer F x) budget q c ((selected_iff F .frozenConstant q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeConstantBits
