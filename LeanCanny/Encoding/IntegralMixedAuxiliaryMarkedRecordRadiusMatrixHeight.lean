/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight

/-! # Actual cleared bank matrix entries have affine radius height -/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access)
open IntegralMixedFramedClearedMatrixBits (rank matrix)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data IntegralMixedAuxiliaryMarkedIntegerPlan.seed

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def matrixSlope (root : List Bool) :=
  ((parameters hn ht ha).cap root + 2) * bankSlope hn ht ha root

noncomputable def matrixOffset (root : List Bool) :=
  ((parameters hn ht ha).cap root + 2) * bankOffset hn ht ha root

theorem matrixSlope_binary : BinaryFn (matrixSlope hn ht ha) :=
  ((BinaryFn.ofUnary (access hn ht ha).cap).add (BinaryFn.const 2)).mul (bankSlope_binary hn ht ha)

theorem matrixOffset_binary : BinaryFn (matrixOffset hn ht ha) :=
  ((BinaryFn.ofUnary (access hn ht ha).cap).add (BinaryFn.const 2)).mul (bankOffset_binary hn ht ha)

theorem matrix_bound (R : List Bool → ℕ) (key : List Bool) (i : ℕ)
    (r s : Fin (rank (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) key)) :
    (matrix (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) key i r s).natAbs ≤
      2 ^ (matrixSlope hn ht ha (pairFst key) * R (pairFst key) + matrixOffset hn ht ha (pairFst key)) := by
  have H := IntegralMixedFramedSlackMatrixBounds.base_bound (parameters hn ht ha) (plan hn ht ha R)
    (data hn ht ha R) key _ (bank_bounds hn ht ha R key) i r s
  have HB : (IntegralMixedFramedClearedMatrixBits.family (parameters hn ht ha)
      (plan hn ht ha R) (data hn ht ha R)).birth key ≤ (parameters hn ht ha).cap (pairFst key) + 1 :=
    (IntegralMixedFramedHistoryFamilyBits.family (parameters hn ht ha)
      (plan hn ht ha R) (data hn ht ha R)).birth_bound key
  apply H.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HT := Nat.mul_le_mul_right
    (bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key)) HB
  unfold IntegralMixedFramedSlackMatrixBounds.baseHeight matrixSlope matrixOffset
  nlinarith only [HT]

theorem certified_matrix_bound {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) (i : ℕ)
    (r s : Fin (rank (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR) key)) :
    (matrix (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR) key i r s).natAbs ≤
      2 ^ (matrixSlope hn ht ha (pairFst key) * R (pairFst key) + matrixOffset hn ht ha (pairFst key)) := by
  have H := IntegralMixedFramedSlackMatrixBounds.base_bound
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR) key _
    (certified_bank_bounds hn ht ha hR key) i r s
  have HB : (IntegralMixedFramedClearedMatrixBits.family
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)).birth key ≤
        (parameters hn ht ha).cap (pairFst key) + 1 :=
    (IntegralMixedFramedHistoryFamilyBits.family
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)).birth_bound key
  apply H.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HT := Nat.mul_le_mul_right
    (bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key)) HB
  unfold IntegralMixedFramedSlackMatrixBounds.baseHeight matrixSlope matrixOffset
  nlinarith only [HT]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
