/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusMatrixHeight

/-! # Affine radius bounds for every actual marked raw-cut and top matrix -/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev actualFamily (R : List Bool → ℕ) :=
  IntegralMixedFramedHistoryFamilyBits.family (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)

theorem fallback_bounds (R : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds (parameters hn ht ha) (plan hn ht ha R)
      (data hn ht ha R) (fun _ => 3) (seed hn ht ha R) key :=
  IntegralMixedSourceIntegerRecordAppend.fallback_bounds (parameters hn ht ha)
    (fun root _ => IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _ => IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha) (fun c => number n c + 8)
    (IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha) (fun _ => le_rfl)
    (fun _ => 3) (seed hn ht ha R) (fun _ => by decide) key

noncomputable def originalBounds (R : List Bool → ℕ) :
    IntegralMixedCoordinateBounds.OriginalBounds (actualFamily hn ht ha R) :=
  IntegralMixedFramedOriginalBounds.originalBounds (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha) (fallback_bounds hn ht ha R)

noncomputable def rawFactor (root : List Bool) :=
  IntegralMixedFramedRawHeight.rootFactor (parameters hn ht ha) (fun _ => 3) root * (factor hn ht ha root + 2)

noncomputable def rawSlope (root : List Bool) := rawFactor hn ht ha root * bankSlope hn ht ha root
noncomputable def rawOffset (root : List Bool) := rawFactor hn ht ha root * bankOffset hn ht ha root

theorem rawFactor_binary : BinaryFn (rawFactor hn ht ha) :=
  (IntegralMixedFramedRawHeight.rootFactor_binary (parameters hn ht ha) (access hn ht ha) (BinaryFn.const 3)).mul
    ((IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha).add (BinaryFn.const 2))

theorem rawSlope_binary : BinaryFn (rawSlope hn ht ha) :=
  (rawFactor_binary hn ht ha).mul (bankSlope_binary hn ht ha)

theorem rawOffset_binary : BinaryFn (rawOffset hn ht ha) :=
  (rawFactor_binary hn ht ha).mul (bankOffset_binary hn ht ha)

theorem raw_ceiling_affine (R : List Bool → ℕ) (root : List Bool) :
    IntegralMixedFramedRawHeight.rootCeiling (parameters hn ht ha) (fun _ => 3) (factor hn ht ha)
      (seed hn ht ha R) root = rawSlope hn ht ha root * R root + rawOffset hn ht ha root := by
  unfold IntegralMixedFramedRawHeight.rootCeiling height rawSlope rawOffset rawFactor
    bankSlope bankOffset amplification seed
  ring

theorem raw_coefficient_bound (R : List Bool → ℕ) (key : List Bool) (k : ℕ)
    (r s : Fin (count ((actualFamily hn ht ha R).birth key) ((actualFamily hn ht ha R).width key))) :
    (IntegralMixedCutMatrix.coefficientMatrix ((actualFamily hn ht ha R).state key)
      ((actualFamily hn ht ha R).birth_bound key) ((actualFamily hn ht ha R).rule key)
      ((actualFamily hn ht ha R).kind key) k r s).natAbs ≤
      2 ^ (rawSlope hn ht ha (pairFst key) * R (pairFst key) + rawOffset hn ht ha (pairFst key)) := by
  have H := IntegralMixedFramedRawHeight.coefficient_root_height (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (familyInputs hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha)
    (fallback_bounds hn ht ha R) key k r s
  rw [raw_ceiling_affine] at H
  exact H

theorem top_bound (R : List Bool → ℕ) (key : List Bool)
    (r s : Fin (IntegralMixedNormalizationTopBits.dimension (actualFamily hn ht ha R) key)) :
    (IntegralMixedNormalizationTopBits.top (actualFamily hn ht ha R) key r s).natAbs ≤
      2 ^ (rawSlope hn ht ha (pairFst key) * R (pairFst key) + rawOffset hn ht ha (pairFst key)) := by
  have H := IntegralMixedFramedRawHeight.top_root_height (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (familyInputs hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha)
    (fallback_bounds hn ht ha R) key r s
  rw [raw_ceiling_affine] at H
  exact H

theorem natural_top_bound (R : List Bool → ℕ) (key : List Bool) (r s : ℕ) :
    (IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedNormalizationTopBits.top (actualFamily hn ht ha R) key) r s).natAbs ≤
      2 ^ (rawSlope hn ht ha (pairFst key) * R (pairFst key) + rawOffset hn ht ha (pairFst key)) := by
  have H := IntegralMixedFramedRawHeight.natural_top_root_height (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (familyInputs hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha)
    (fallback_bounds hn ht ha R) key r s
  rw [raw_ceiling_affine] at H
  exact H

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
