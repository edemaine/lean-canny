/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
public import LeanCanny.Algebra.IntegralCriticalFlatMoment
/-! # Actual valid creating-source dimensions fit the flat query cap -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualCaps
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem free_le (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalTotalCreatingBits.euler F).free q ≤ F.ambient (root q) + 1 := by
  change (IntegralCriticalTotalCreatingBits.atFamily F q).free [] + 1 ≤ _
  rw [IntegralCriticalTotalCreatingBits.at_free, ite_eq_left h]
  exact Nat.add_le_add_right (Nat.sub_le _ _) 1

theorem degree_le (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalTotalCreatingBits.euler F).degree q ≤ F.degree (root q) := by
  change ((IntegralCriticalTotalCreatingBits.atFamily F q).data []).degree ≤ _
  rw [IntegralCriticalTotalCreatingBits.at_degree, ite_eq_left h, commandDegree_creating F q h]
  exact (IntegralCriticalScript.chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)).degree_le

theorem rank_le (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.characteristic F).rank q ≤ IntegralCriticalHistoryTask.rankCap F.toParameters (root q) := by
  change IntegralCriticalTotalCreatingBits.rank F q ≤ _
  rw [IntegralCriticalTotalCreatingBits.at_rank, ite_eq_left h]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (min_le_right _ _)

theorem dimension_eq (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatActualSources.characteristic F).dimension q = PurePowerReductionBounds.dimension
      ((IntegralCriticalTotalCreatingBits.euler F).free q) ((IntegralCriticalTotalCreatingBits.euler F).degree q) := rfl

theorem dimension_le (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.characteristic F).dimension q ≤
      PurePowerReductionBounds.dimension (F.ambient (root q) + 1) (F.degree (root q)) := by
  rw [dimension_eq]
  exact IntegralCriticalFactorCeiling.dimension_mono (free_le F q h) (degree_le F q h)

theorem rank_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.characteristic F).rank q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  (rank_le F q h).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem dimension_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.characteristic F).dimension q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  (dimension_le F q h).trans (IntegralCriticalQueryBounds.spatial_grid_le _ _ _ _ _ _ _ _)

theorem coefficient_block_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatActualSources.characteristic F) q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  IntegralCriticalQueryBounds.coefficient_block_le_of_le _ _ _ _ _ _ _ _ (dimension_le F q h) (rank_le F q h)

theorem action_block_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.characteristic F).dimension q * (IntegralCriticalFlatActualSources.characteristic F).rank q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  (Nat.mul_le_mul (dimension_le F q h) (rank_le F q h)).trans (IntegralCriticalQueryBounds.action_block_le _ _ _ _ _ _ _ _)

theorem reduction_block_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.reduction F).dimension q * (IntegralCriticalFlatActualSources.reduction F).rank q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := action_block_cap F q h

theorem moment_dimension_le (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).dimension q ≤
      (IntegralCriticalFlatActualSources.characteristic F).dimension q := by
  change IntegralBerkowitzBlockBits.remaining (IntegralCriticalFlatActualSources.characteristic F)
    (IntegralCriticalFlatMomentBits.packet F.toParameters q) ≤ _
  unfold IntegralBerkowitzBlockBits.remaining
  rw [IntegralCriticalFlatMomentBits.packet_parent]
  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem moment_block_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    ((IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).dimension q + 2) *
      (IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).rank q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := by
  have HM := (moment_dimension_le F q).trans (dimension_le F q h)
  have HR : (IntegralCriticalFlatMomentBits.source F.toParameters (IntegralCriticalFlatActualSources.characteristic F)).rank q =
      (IntegralCriticalFlatActualSources.characteristic F).rank q := by
    change (IntegralCriticalFlatActualSources.characteristic F).rank (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet F.toParameters q)) = _
    rw [IntegralCriticalFlatMomentBits.packet_parent]
  rw [HR]
  exact (Nat.mul_le_mul (Nat.add_le_add_right HM 2) (rank_le F q h)).trans
    (IntegralCriticalQueryBounds.moment_block_le _ _ _ _ _ _ _ _)

theorem original_grid_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    count ((IntegralCriticalTotalCreatingBits.euler F).arity q) ((IntegralCriticalTotalCreatingBits.euler F).sourceWidth q) ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := by
  change count ((IntegralCriticalTotalCreatingBits.atFamily F q).ambient [] + 1)
    ((IntegralCriticalTotalCreatingBits.atFamily F q).sourceWidth []) ≤ _
  simp only [IntegralCriticalTotalCreatingBits.at_ambient, IntegralCriticalTotalCreatingBits.at_sourceWidth, ite_eq_left h]
  exact IntegralCriticalQueryBounds.source_grid_le _ _ _ _ _ _ _ _

theorem target_grid_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    count ((IntegralCriticalTotalCreatingBits.euler F).free q) ((IntegralCriticalTotalCreatingBits.euler F).targetWidth q) ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := dimension_cap F q h

theorem reduction_exponent_cap (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatActualSources.reduction F).bound q + 1 ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := by
  have H : (IntegralCriticalFlatActualSources.reduction F).bound q ≤
      PurePowerReductionBounds.bound (F.ambient (root q) + 1) (F.degree (root q)) := by
    change PurePowerReductionBounds.bound ((IntegralCriticalTotalCreatingBits.euler F).free q)
      ((IntegralCriticalTotalCreatingBits.euler F).degree q) ≤ _
    unfold PurePowerReductionBounds.bound
    exact Nat.add_le_add_right (Nat.mul_le_mul (free_le F q h) (Nat.sub_le_sub_right (degree_le F q h) 1)) 1
  exact (Nat.add_le_add_right H 1).trans (IntegralCriticalQueryBounds.reduction_exponent_le _ _ _ _ _ _ _ _)
end LeanCanny.Algebra.IntegralCriticalActualCaps
