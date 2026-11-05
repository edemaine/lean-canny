/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality

/-! # Structural source selectors for actual cross-context field comparisons

Chronological labels select one LEFT characteristic polynomial. Both probes
retain their own context and word and request derivatives of that same source.
The structural selectors have no radius argument.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}

def catalogCount (n : List Bool → ℕ) (c : List Bool) := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst c)
def catalogSelected (n : List Bool → ℕ) (right : Bool) (z : List Bool) :=
  newest (catalogCount n (context right z)) (label right z)
def catalogOldArgument (n : List Bool → ℕ) (z : List Bool) :=
  pair (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context false z))
    (BinaryNatCode.encode (catalogSelected n false z))
def catalogProbe (n : List Bool → ℕ) (right : Bool) (z : List Bool) (k : ℕ) :=
  pair (sample right z) (pair (catalogOldArgument n z)
    (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k)))

variable (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem family_width (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := by
  unfold IntegralMixedFramedHistoryFamilyBits.family
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

theorem bank_key_catalog (c : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key c = IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  simp only [IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false, IntegralMixedAuxiliaryMarkedRecordPlan.bank]

theorem count_catalog (c : List Bool) : count hn ht ha hR c = catalogCount n c := by
  simp only [count, catalogCount, IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank]
  exact IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha hR c

theorem selected_catalog (right : Bool) (z : List Bool) :
    selected hn ht ha hR right z = catalogSelected n right z := by
  unfold selected catalogSelected
  rw [count_catalog]

theorem oldArgument_catalog (z : List Bool) : oldArgument hn ht ha hR z = catalogOldArgument n z := by
  unfold oldArgument catalogOldArgument
  rw [bank_key_catalog, selected_catalog]

theorem probe_catalog (right : Bool) (z : List Bool) (k : ℕ) :
    probe hn ht ha hR right (pair z (BinaryNatCode.encode k)) = catalogProbe n right z k := by
  simp only [probe, pairFst_pair, pairSnd_pair, oldArgument_catalog, selected_catalog, catalogProbe]

theorem derivative_key_catalog (right : Bool) (z : List Bool) (k : ℕ) :
    derivativePacket (probe hn ht ha hR right (pair z (BinaryNatCode.encode k))) =
      pair (catalogOldArgument n z) (BinaryNatCode.encode k) := by
  rw [probe_catalog]
  simp only [derivativePacket, catalogProbe, pairFst_pair, pairSnd_pair]

theorem source_polynomial_catalog (c : List Bool) :
    (originalSource hn ht ha hR).polynomial c =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) c := by
  simp only [originalSource, IntegralMixedPhysicalCriticalBankEquality.originalSource,
    IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false, IntegralMixedAuxiliaryMarkedRecordPlan.bank,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource]
  rfl

theorem derivative_polynomial_catalog (right : Bool) (z : List Bool) (k : ℕ) :
    (derivatives hn ht ha hR).polynomial (probe hn ht ha hR right (pair z (BinaryNatCode.encode k))) =
      Polynomial.derivative^[k] (IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
        (catalogOldArgument n z)) := by
  change (IntegerPolynomialIteratedDerivativeBits.source (originalSource hn ht ha hR)).polynomial
    (derivativePacket (probe hn ht ha hR right (pair z (BinaryNatCode.encode k)))) = _
  rw [derivative_key_catalog, IntegerPolynomialIteratedDerivativeBits.packet, source_polynomial_catalog]

theorem argument_root_catalog (z : List Bool) :
    pairFst (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogOldArgument n z)) =
      pairFst (context false z) := by
  simp only [IntegralMixedFramedCoordinateCharacteristicBits.key, catalogOldArgument,
    IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]

theorem characteristic_count_catalog (z : List Bool) :
    IntegralMixedFramedCoordinateCharacteristicBits.count
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR) (catalogOldArgument n z) =
      catalogCount n (context false z) := by
  simpa only [IntegralMixedFramedCoordinateCharacteristicBits.count,
    IntegralMixedFramedCoordinateCharacteristicBits.key, catalogOldArgument, pairFst_pair,
    IntegralMixedFramedBankSnapshotBits.atKey, catalogCount] using
    IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha hR (context false z)

theorem characteristic_width_catalog (z : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family (certifiedParameters hn ht ha hR)
      (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).width
        (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogOldArgument n z)) =
      (parameters hn ht ha).width (pairFst (context false z)) := by
  rw [family_width, argument_root_catalog]
  rfl

noncomputable def catalogDegree (root : List Bool) :=
  FixedWidthPolynomial.count (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) ((parameters hn ht ha).width root)

theorem degree_catalog (z : List Bool) :
    degree hn ht ha hR z = catalogDegree hn ht ha (pairFst (context false z)) := by
  unfold degree
  change IntegralMixedFramedCoordinateCharacteristicBits.dimension
    (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
    (oldArgument hn ht ha hR z) = _
  rw [oldArgument_catalog]
  unfold IntegralMixedFramedCoordinateCharacteristicBits.dimension
  rw [characteristic_count_catalog, characteristic_width_catalog]
  rfl

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
