/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualGradientSnapshot
/-! # Actual scalar replies under fresh spatial task writers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualSpatialTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualGradientSnapshot
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatEulerRowsBits.spatial

noncomputable def cleared (F : Scripts) (q : List Bool) :=
  (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).value q

theorem derivative_snapshot (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatGridSourceBits.derivative F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).value q =
      gradient (IntegralCriticalTotalCreatingBits.atFamily F q)
        (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
        (IntegralCriticalHistoryTask.get F.toParameters .target q)
        (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := rfl

theorem cleared_original (F : Scripts) (q : List Bool)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression q ≠ 1) :
    cleared F q = original (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .target q)
      (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  unfold cleared IntegralCriticalFlatGenericGridBits.source
  rw [IntegralCriticalFlatGridSourceBits.value]
  change (if IntegralCriticalHistoryTask.get F.toParameters .expression q = 1 then _ else _) = _
  rw [ite_eq_right hx, original_snapshot]

theorem cleared_derivative (F : Scripts) (q : List Bool)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression q = 1) :
    cleared F q = gradient (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
      (IntegralCriticalHistoryTask.get F.toParameters .target q)
      (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  unfold cleared IntegralCriticalFlatGenericGridBits.source
  rw [IntegralCriticalFlatGridSourceBits.value]
  change (if IntegralCriticalHistoryTask.get F.toParameters .expression q = 1 then _ else _) = _
  rw [ite_eq_left hx, derivative_snapshot]

theorem spatial_creator (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (x : ℕ)
    (q : List Bool) (j e : ℕ) :
    IntegralCriticalTotalCreatingBits.atFamily F
      (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase x
        (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))) =
    IntegralCriticalTotalCreatingBits.atFamily F q := by
  apply IntegralCriticalTotalCreatingBits.atFamily_invariance
  · simpa only [root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatEulerRowsBits.spatial_root F.toParameters phase x
        (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_birth F.toParameters phase x
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))

theorem spatial_derivative_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase)
    (q : List Bool) (j : Fin ((IntegralCriticalTotalCreatingBits.euler F).free q)) (e : ℕ)
    (hj : j.val ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q))
    (he : e ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    cleared F (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))) =
    (IntegralCriticalGradientBits.family (IntegralCriticalTotalCreatingBits.euler F).toGradient).value
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) := by
  let child := IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase 1
    (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields F.toParameters phase 1 q j.val e hj he
    (IntegralCriticalHistoryTask.numericCap_pos F.toParameters _)
  change cleared F child = _
  rw [cleared_derivative F child HF.2.2, gradient_snapshot F q j e]
  apply gradient_congr
  · exact spatial_creator F phase 1 q j.val e
  · exact HF.1
  · exact HF.2.1
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) .row (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) .col (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus F.toParameters phase 1
      (pair q (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))


theorem spatial_original_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase)
    (q : List Bool) (j e : ℕ)
    (hj : j ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q))
    (he : e ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    cleared F (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))) =
    original (IntegralCriticalTotalCreatingBits.atFamily F q) e
      (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) := by
  let child := IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase 0
    (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields F.toParameters phase 0 q j e hj he (Nat.zero_le _)
  change cleared F child = _
  rw [cleared_original F child (by rw [HF.2.2]; decide)]
  apply original_congr
  · exact spatial_creator F phase 0 q j e
  · exact HF.2.1
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e))) .row (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e))) .col (by decide) (by decide) (by decide)
  · simpa only [child, pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))

theorem frozenLower_cleared_child (F : Scripts) (q : List Bool) :
    cleared F (IntegralCriticalFlatFrozenLowerBits.clearedTask F.toParameters
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen q) =
    (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.toSource.value q := by
  rw [original_snapshot]
  exact spatial_original_child F .clearedGridSum q _ _
    (IntegralCriticalHistoryTask.get_le F.toParameters .derivative q)
    (IntegralCriticalHistoryTask.get_le F.toParameters .target q)

theorem selected_cap (F : Scripts) (q : List Bool)
    (j : Fin ((IntegralCriticalTotalCreatingBits.euler F).free q)) :
    j.val ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  have HF := (IntegralCriticalTotalCreatingBits.euler F).fit q
  have HA := IntegralCriticalActualScalarModels.arity_cap F q
  have HJ := j.isLt
  omega

theorem lower_gradient_child (F : Scripts) (q : List Bool) :
    cleared F (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters .clearedGridSum 1
      (IntegralCriticalFlatEulerRowsBits.packet F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q)) =
    (IntegralCriticalGradientBits.family (IntegralCriticalTotalCreatingBits.euler F).toGradient).value
      (IntegralCriticalFlatEulerRowsBits.packet F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q) :=
  spatial_derivative_child F .clearedGridSum q
    (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q) _
    (selected_cap F q _) (IntegralCriticalHistoryTask.get_le F.toParameters .target q)

theorem product_gradient_child (F : Scripts) (q : List Bool) (hv : valid F q) :
    cleared F (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters .clearedGridSum 1
      (IntegralCriticalFlatEulerRowsBits.productGradientQuery F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q)) =
    (IntegralCriticalGradientBits.family (IntegralCriticalTotalCreatingBits.euler F).toGradient).value
      (IntegralCriticalFlatEulerRowsBits.productGradientQuery F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q) := by
  rw [IntegralCriticalFlatEulerRowsBits.productGradientQuery_eq]
  exact spatial_derivative_child F .clearedGridSum q _ _ (selected_cap F q _)
    ((IntegralCriticalFlatEulerRowsBits.loweredTarget_lt F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q).le.trans
      (IntegralCriticalActualCaps.target_grid_cap F q hv))

end LeanCanny.Algebra.IntegralCriticalActualSpatialTransport
