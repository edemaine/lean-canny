/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native actual Euler lower-polynomial branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeEulerLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.euler F
noncomputable abbrev program (F : Scripts) := IntegralCriticalFlatGenericEulerBits.lowerProgram F.toParameters (source F)
noncomputable abbrev gradient (F : Scripts) := IntegralEulerBits.lowerGradientQuery (source F)
  (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (source F))

theorem certificates (F : Scripts) (h : Controls F) :
    (program F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F).certificates (IntegralCriticalFlatGenericEulerBits.lower_controls F.toParameters h.task.toAccess (source F) (eulerAccess F h))

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofSingleCall (program F) (certificates F h) (selected F .eulerLower) (selected_FP F h .eulerLower)
    (IntegralCriticalActualScalarModels.lower F) (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem gradient_parent (F : Scripts) (q : List Bool) : pairFst (gradient F q) = q := by
  unfold gradient IntegralEulerBits.lowerGradientQuery
  rw [pairFst_pair]

theorem query_eq (F : Scripts) (q : List Bool) : (program F).query q =
    if (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (source F) q).val = IntegralEulerBits.objectiveRank (source F) q then
      IntegralCriticalFlatEulerBits.next F.toParameters .eulerObjective q else
      IntegralCriticalFlatEulerRowsBits.spatial F.toParameters .clearedGridSum 1 (gradient F q) := rfl

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .eulerLower q) (hc : (program F).controller.Requests reply budget q c) : Frame F q c := by
  have H1 := ((program F).requests_iff reply budget q c).mp hc
  apply Eq.mpr (congrArg (Frame F q) H1.2)
  rw [query_eq]
  change phase q = 16 at hp
  split_ifs
  · exact frame_next F .eulerObjective q (by change 15 < phase q; omega)
  · have HP : 8 < phase (pairFst (gradient F q)) := by rw [gradient_parent]; omega
    have HF := frame_spatial F .clearedGridSum 1 (gradient F q) HP
    rw [gradient_parent] at HF
    exact HF

theorem value_at (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) q = IntegralCriticalActualScalarModels.lower F q := by
  apply Eq.trans (IntegralCriticalFlatGenericEulerBits.lower_value_at F.toParameters (source F) (answer F x) q ?_ ?_)
    (IntegralCriticalActualScalarModels.lower_eq F q).symm
  · intro _
    exact (matches_next F x hm .eulerObjective (by decide) q hv).trans (IntegralCriticalActualScalarModels.lower_objective_child F q)
  · intro _
    exact (matches_spatial F x hm .clearedGridSum (by decide) 1 (gradient F q) (by rw [gradient_parent]; exact hv)).trans
      (IntegralCriticalActualSpatialTransport.lower_gradient_child F q)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply single_correct_of_frame F h .eulerLower (program F) (certificates F h) (IntegralCriticalActualScalarModels.lower F) x
  · intro q hq
    exact value_at F x hm q ((selected_iff F .eulerLower q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F (answer F x) budget q c ((selected_iff F .eulerLower q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeEulerLowerBits
