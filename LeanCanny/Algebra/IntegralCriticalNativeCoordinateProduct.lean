/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native coordinate-gradient product branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeCoordinateProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalTotalCreatingBits.euler F
noncomputable abbrev program (F : Scripts) := IntegralCriticalFlatGenericEulerBits.productProgram F.toParameters (source F)
noncomputable abbrev query (F : Scripts) := IntegralCriticalFlatEulerRowsBits.productGradientQuery F.toParameters (source F)

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofSingleCall (program F) ((program F).certificates (IntegralCriticalFlatGenericEulerBits.product_controls F.toParameters h.task.toAccess (source F) (eulerAccess F h)))
    (selected F .coordinateGradientProduct) (selected_FP F h .coordinateGradientProduct) (IntegralCriticalActualProductModel.product F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem query_parent (F : Scripts) (q : List Bool) : pairFst (query F q) = q := by
  unfold query
  rw [IntegralCriticalFlatEulerRowsBits.productGradientQuery_eq, pairFst_pair]

theorem query_eq (F : Scripts) (q : List Bool) : (program F).query q =
    IntegralCriticalFlatEulerRowsBits.spatial F.toParameters .clearedGridSum 1 (query F q) := rfl

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .coordinateGradientProduct q) (hc : (program F).controller.Requests reply budget q c) : Frame F q c := by
  have H1 := ((program F).requests_iff reply budget q c).mp hc
  apply Eq.mpr (congrArg (Frame F q) H1.2)
  rw [query_eq]
  have HP : 8 < phase (pairFst (query F q)) := by
    rw [query_parent]
    change phase q = 13 at hp
    omega
  have HF := frame_spatial F .clearedGridSum 1 (query F q) HP
  rw [query_parent] at HF
  exact HF

theorem value_at (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) q = IntegralCriticalActualProductModel.product F q := by
  have HC := single_value_congr_at (program F) (answer F x) (IntegralCriticalActualSpatialTransport.cleared F) q (by
    intro _
    rw [query_eq]
    exact matches_spatial F x hm .clearedGridSum (by decide) 1 (query F q) (by rw [query_parent]; exact hv))
  have HP := IntegralCriticalFlatGenericEulerBits.product_value_at F.toParameters (source F)
    (IntegralCriticalActualSpatialTransport.cleared F) q (fun _ => IntegralCriticalActualSpatialTransport.product_gradient_child F q hv)
  have HM : (if (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (source F) q).val =
        IntegralEulerBits.objectiveRank (source F) q then [] else IntegralCriticalCoordinateProductBits.value (source F).toGradient
      (IntegralCriticalFlatEulerRowsBits.packet F.toParameters (source F) q)) = IntegralCriticalActualProductModel.product F q := by
    simpa only [IntegralEulerBits.objectiveRank, Fin.ext_iff] using (IntegralCriticalActualProductModel.product_eq F q).symm
  exact HC.trans (HP.trans HM)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply single_correct_of_frame F h .coordinateGradientProduct (program F)
    ((program F).certificates (IntegralCriticalFlatGenericEulerBits.product_controls F.toParameters h.task.toAccess (source F) (eulerAccess F h)))
    (IntegralCriticalActualProductModel.product F) x
  · intro q hq
    exact value_at F x hm q ((selected_iff F .coordinateGradientProduct q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F (answer F x) budget q c ((selected_iff F .coordinateGradientProduct q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeCoordinateProductBits
