/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityCatalog
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow

/-! # Actual field-comparison characteristic and derivative radius profiles

The source is the actual LEFT cleared-coordinate characteristic polynomial.
All derivative orders, including zero, retain that source and its own root.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData access)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (bankSlope bankOffset bankSlope_binary bankOffset_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem catalogDegree_binary : BinaryFn (catalogDegree hn ht ha) :=
  ((BinaryFn.const 2).powUnary (access hn ht ha).width).powUnary
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount_unary hn)

noncomputable def fieldSlope (root : List Bool) :=
  (2 * IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root + 1) * catalogDegree hn ht ha root * bankSlope hn ht ha root
noncomputable def fieldOffset (root : List Bool) :=
  IntegralMixedBankCoordinatePolynomial.massBudget (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root)
    ((parameters hn ht ha).width root) (bankOffset hn ht ha root)
noncomputable def derivativeOffset (root : List Bool) :=
  IteratedDerivativeBits.massBudget (catalogDegree hn ht ha root) (fieldOffset hn ht ha root)

theorem fieldSlope_binary : BinaryFn (fieldSlope hn ht ha) :=
  ((((BinaryFn.const 2).mul (BinaryFn.ofUnary (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount_unary hn))).add
    (BinaryFn.const 1)).mul (catalogDegree_binary hn ht ha)).mul (bankSlope_binary hn ht ha)

theorem fieldOffset_binary : BinaryFn (fieldOffset hn ht ha) :=
  IntegralMixedBankCoordinatePolynomial.massBudget_binary
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount_unary hn) (access hn ht ha).width (bankOffset_binary hn ht ha)

theorem derivativeOffset_binary : BinaryFn (derivativeOffset hn ht ha) :=
  IteratedDerivativeBits.massBudget_binary (catalogDegree_binary hn ht ha) (fieldOffset_binary hn ht ha)

private theorem mass_of_bank (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) (G : ℕ)
    (HB : ((IntegralMixedFramedHistoryFamilyBits.family P D H).state
      (IntegralMixedFramedCoordinateCharacteristicBits.key c)).bank.Bounds G) :
    coefficientMass (IntegralMixedFramedCoordinateCharacteristicBits.polynomial P D H c) ≤
      2 ^ IntegralMixedBankCoordinatePolynomial.massBudget
        (IntegralMixedFramedCoordinateCharacteristicBits.count P D H c)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).width
          (IntegralMixedFramedCoordinateCharacteristicBits.key c)) G := by
  have HM := ScaledCharacteristicIntegerBounds.mass_bound
    (IntegralMixedFramedCoordinateCharacteristicBits.matrix P D H c)
    (IntegralMixedFramedCoordinateCharacteristicBits.common P D H c)
    (G + IntegralMixedFramedCoordinateCharacteristicBits.count P D H c * G)
    (IntegralMixedFramedCoordinateCharacteristicBits.count P D H c * G)
    (IntegralMixedFramedCoordinateCharacteristicBits.common_ne_zero P D H c)
    (IntegralMixedFramedCoordinateCharacteristicBits.matrix_bound P D H c G HB)
    (IntegralMixedFramedCoordinateCharacteristicBits.common_bound P D H c G HB)
  simpa only [IntegralMixedFramedCoordinateCharacteristicBits.polynomial, ScaledCharacteristicIntegerBounds.massHeight,
    ScaledCharacteristicIntegerBounds.coefficientHeight, IntegralMixedFramedCoordinateCharacteristicBits.dimension,
    IntegralMixedBankCoordinatePolynomial.massBudget, IntegralMixedBankCoordinatePolynomial.coefficientBudget] using HM

private theorem budget_affine (m B K H r : ℕ) :
    IntegralMixedBankCoordinatePolynomial.massBudget m B (K * r + H) =
      ((2 * m + 1) * FixedWidthPolynomial.count m B * K) * r +
        IntegralMixedBankCoordinatePolynomial.massBudget m B H := by
  unfold IntegralMixedBankCoordinatePolynomial.massBudget IntegralMixedBankCoordinatePolynomial.coefficientBudget
    CharacteristicIntegerBounds.budget
  ring

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

theorem source_mass {R : List Bool → ℕ} (hR : BinaryFn R) (z : List Bool) :
    coefficientMass ((originalSource hn ht ha hR).polynomial (oldArgument hn ht ha hR z)) ≤
      2 ^ (fieldSlope hn ht ha (pairFst (context false z)) * R (pairFst (context false z)) +
        fieldOffset hn ht ha (pairFst (context false z))) := by
  rw [source_polynomial_catalog, oldArgument_catalog]
  have HM := mass_of_bank (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) (catalogOldArgument n z) _
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_bank_bounds hn ht ha hR
      (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogOldArgument n z)))
  rw [characteristic_count_catalog, characteristic_width_catalog, argument_root_catalog, budget_affine] at HM
  exact HM

theorem derivative_mass {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
    coefficientMass ((derivatives hn ht ha hR).polynomial
      (probe hn ht ha hR right (pair z (BinaryNatCode.encode k)))) ≤
      2 ^ (fieldSlope hn ht ha (pairFst (context false z)) * R (pairFst (context false z)) +
        derivativeOffset hn ht ha (pairFst (context false z))) := by
  rw [derivative_polynomial_catalog]
  have HB := source_mass hn ht ha hR z
  rw [source_polynomial_catalog, oldArgument_catalog] at HB
  have HD : (IntegralMixedFramedCoordinateCharacteristicBits.polynomial
      (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)
      (catalogOldArgument n z)).natDegree ≤ catalogDegree hn ht ha (pairFst (context false z)) := by
    rw [IntegralMixedFramedCoordinateCharacteristicBits.degree,
      IntegralMixedFramedCoordinateCharacteristicBits.dimension, characteristic_count_catalog, characteristic_width_catalog]
    exact le_rfl
  have HM := IteratedDerivativeBits.mass_bound _ _ _ HD
    (fun i => (coeff_natAbs_le_coefficientMass _ i).trans HB) k
  exact HM.trans (Nat.pow_le_pow_right (by decide) (by simp only [derivativeOffset, IteratedDerivativeBits.massBudget]; omega))

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
