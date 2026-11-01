/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFolds
/-! # Native virtual coordinate-gradient products with an actual cleared child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev coordinateProgram (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericEulerBits.productProgram P (source P F)
noncomputable abbrev coordinateQuery (P : Parameters) (F : Family) :=
  IntegralCriticalFlatEulerRowsBits.productGradientQuery P (source P F)

abbrev CoordinateRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  (coordinateProgram P F).request q = true → reply ((coordinateProgram P F).query q) =
    IntegralMixedVirtualSpatialBits.cleared P F ((coordinateProgram P F).query q)

theorem coordinate_model (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualFoldBits.product P F q =
      if (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val = IntegralEulerBits.objectiveRank (source P F) q then []
      else IntegralCriticalCoordinateProductBits.value (source P F).toGradient (IntegralCriticalFlatEulerRowsBits.packet P (source P F) q) := by
  rw [IntegralMixedVirtualFoldBits.product_eq_term]
  have HX : IntegralEulerBits.excluded (source P F)
      (pair q (BinaryNatCode.encode (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val)) ↔
      (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val = IntegralEulerBits.objectiveRank (source P F) q := by
    unfold IntegralEulerBits.excluded IntegralEulerBits.objectiveRank
    rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold IntegralEulerBits.termProgram
  simp only [HX]
  simp only [IntegralEulerBits.termQuery, pairFst_pair, pairSnd_pair]
  rfl

theorem coordinate_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedVirtualSpatialBits.cleared P F ((coordinateProgram P F).query q) =
      (IntegralCriticalGradientBits.family (source P F).toGradient).value (coordinateQuery P F q) := by
  change IntegralMixedVirtualSpatialBits.cleared P F
    (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (coordinateQuery P F q)) = _
  unfold coordinateQuery
  rw [IntegralCriticalFlatEulerRowsBits.productGradientQuery_eq]
  exact IntegralMixedVirtualSpatialBits.spatial_derivative_child P F .clearedGridSum q _ _
    (IntegralCriticalFlatEulerRowsBits.selected_le P (source P F) q)
    ((IntegralCriticalFlatEulerRowsBits.loweredTarget_lt P (source P F) q).le.trans
      (IntegralMixedVirtualFoldBits.target_grid_cap P F g q))

theorem coordinate_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : CoordinateRepliesAt P F reply q) :
    (coordinateProgram P F).request q = true → reply ((coordinateProgram P F).query q) =
      (IntegralCriticalGradientBits.family (source P F).toGradient).value (coordinateQuery P F q) :=
  fun hr => (he hr).trans (coordinate_child P F g q)

theorem coordinate_value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : CoordinateRepliesAt P F reply q) :
    (coordinateProgram P F).value reply q = IntegralMixedVirtualFoldBits.product P F q :=
  (IntegralCriticalFlatGenericEulerBits.product_value_at P (source P F) reply q
    (fun hr => (he hr).trans (coordinate_child P F g q))).trans (coordinate_model P F q).symm

noncomputable def coordinateMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (coordinateProgram P F).controller
  certificates := (coordinateProgram P F).certificates (IntegralCriticalFlatGenericEulerBits.product_controls P a (source P F) (sourceAccess P a F h))
  selected := selectedValid P .coordinateGradientProduct
  selected_FP := selectedValid_FP P a .coordinateGradientProduct
  model := IntegralMixedVirtualFoldBits.product P F
  clock := fun _ => 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralCriticalFlatGenericEulerBits.lowerStateBound (source P F)
  stateBound_unary := IntegralCriticalFlatGenericEulerBits.lowerStateBound_unary _ (sourceAccess P a F h)

theorem coordinate_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .coordinateGradientProduct q = true → CoordinateRepliesAt P F reply q) :
    Correct (coordinateMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (coordinateProgram P F).halted_after reply q
  · intro q t hq hh
    simp only [coordinateMachine] at hh ⊢
    exact (IntegralCriticalFlatGenericEulerBits.product_output_when_halted_at P (source P F) reply q
      (coordinate_reply P F g reply q (he q hq)) t hh).trans (coordinate_model P F q).symm
  · intro q t hq
    exact IntegralCriticalFlatGenericEulerBits.product_state_length_at P (source P F) reply q
      (coordinate_reply P F g reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .coordinateGradientProduct q).mp hq).2.2
    have HC := ((coordinateProgram P F).requests_iff reply budget q c).mp hc
    have HO : pairFst (coordinateQuery P F q) = q := IntegralCriticalFlatEulerRowsBits.productGradientQuery_parent P (source P F) q
    have HF := frame_spatial P .clearedGridSum 1 (coordinateQuery P F q)
    rw [HO] at HF
    apply Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) HC.2)
    exact HF (by change phase q = 13 at HP; change 8 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
