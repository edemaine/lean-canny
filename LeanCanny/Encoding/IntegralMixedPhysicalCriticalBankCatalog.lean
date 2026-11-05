/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityPlanning
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankReadback

/-! # The actual critical-probe comparison uses one original parent prefix

The marked mode is fixed to false. Parent and child remain at their own
consecutive samplers under the same prepared root. Only structural keys and
advertised dimensions are identified; no complete words are transported.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- Literal saved parent key, independent of the radius reader and both words. -/
def catalogArgument (n : List Bool → ℕ) (q : List Bool) (i : ℕ) :=
  pair (IntegralMixedPhysicalCriticalPrefixes.key n false false q) (BinaryNatCode.encode i)

noncomputable def catalogDegree (q : List Bool) :=
  FixedWidthPolynomial.count (IntegralMixedPhysicalCriticalPrefixes.birth n false false q)
    ((parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q))

private theorem family_width (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := by
  unfold IntegralMixedFramedHistoryFamilyBits.family
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

variable {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem bank_false : IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false =
    IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hR := rfl

theorem source_polynomial_catalog (q : List Bool) (i : ℕ) :
    (source hn ht ha hR false).polynomial (pair q (BinaryNatCode.encode i)) =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial (certifiedParameters hn ht ha hR)
        (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (catalogArgument n q i) := by
  simp only [source, originalSource, IntegerPolynomialSourceChoice.reindex, Function.comp_apply, saved,
    pairFst_pair, pairSnd_pair, catalogArgument, bank_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedFramedCoordinateCharacteristicBits.rootSource]

theorem source_polynomial_base (q : List Bool) (i : ℕ) :
    (source hn ht ha hR false).polynomial (pair q (BinaryNatCode.encode i)) =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial (parameters hn ht ha)
        (plan hn ht ha R) (data hn ht ha R) (catalogArgument n q i) := by
  simpa only [source, IntegerPolynomialSourceChoice.reindex, Function.comp_apply, saved,
    pairFst_pair, pairSnd_pair, catalogArgument, IntegralMixedPhysicalFieldEquality.originalSource] using
    IntegralMixedPhysicalFieldEquality.source_polynomial_base hn ht ha hR (catalogArgument n q i)

theorem derivative_polynomial_base (q : List Bool) (i k : ℕ) :
    (derivatives hn ht ha hR false).polynomial
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (catalogArgument n q i)) := by
  rw [derivative_polynomial, source_polynomial_base]

theorem argument_root_catalog (q : List Bool) (i : ℕ) :
    pairFst (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogArgument n q i)) =
      IntegralMixedPhysicalCriticalQuery.root q := by
  simp only [catalogArgument, IntegralMixedFramedCoordinateCharacteristicBits.key,
    IntegralMixedPhysicalCriticalPrefixes.key, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]

theorem characteristic_count_catalog (q : List Bool) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.count (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (catalogArgument n q i) =
      IntegralMixedPhysicalCriticalPrefixes.birth n false false q := by
  have HK := IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false q
  rw [bank_false] at HK
  simpa only [IntegralMixedFramedCoordinateCharacteristicBits.count,
    IntegralMixedFramedCoordinateCharacteristicBits.key, catalogArgument, pairFst_pair,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank] using HK

theorem characteristic_width_catalog (q : List Bool) (i : ℕ) :
    (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).width
        (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogArgument n q i)) =
      (parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q) := by
  rw [family_width, argument_root_catalog]
  rfl

theorem degree_catalog (z : List Bool) (i : ℕ) :
    degree hn ht ha hR false (pair z (List.replicate i true)) = catalogDegree hn ht ha (pairFst z) := by
  simp only [degree, source, originalSource, IntegerPolynomialSourceChoice.reindex, Function.comp_apply,
    saved, pairFst_pair, pairSnd_pair, List.length_replicate,
    bank_false, IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedFramedCoordinateCharacteristicBits.rootSource]
  change IntegralMixedFramedCoordinateCharacteristicBits.dimension
    (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      (catalogArgument n (pairFst z) i) = _
  unfold IntegralMixedFramedCoordinateCharacteristicBits.dimension
  rw [characteristic_count_catalog, characteristic_width_catalog]
  rfl

theorem catalogDegree_binary : BinaryFn (catalogDegree hn ht ha) :=
  ((BinaryFn.const 2).powUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp
    pairFst_mem_FP)).powUnary (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn false false)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
