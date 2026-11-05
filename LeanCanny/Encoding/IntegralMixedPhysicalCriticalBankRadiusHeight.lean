/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankCatalog
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow

/-! # Actual critical-parent characteristic and derivative radius profiles

The native source remains the saved parent prefix, rather than the full bank.
All derivative orders are covered, including zero and above-degree requests.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (bankSlope bankOffset bankSlope_binary bankOffset_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def fieldSlope (q : List Bool) :=
  (2 * IntegralMixedPhysicalCriticalPrefixes.birth n false false q + 1) * catalogDegree hn ht ha q *
    bankSlope hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
noncomputable def fieldOffset (q : List Bool) :=
  IntegralMixedBankCoordinatePolynomial.massBudget (IntegralMixedPhysicalCriticalPrefixes.birth n false false q)
    ((parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q))
    (bankOffset hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
noncomputable def derivativeOffset (q : List Bool) :=
  IteratedDerivativeBits.massBudget (catalogDegree hn ht ha q) (fieldOffset hn ht ha q)

theorem fieldSlope_binary : BinaryFn (fieldSlope hn ht ha) :=
  ((((BinaryFn.const 2).mul (BinaryFn.ofUnary (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn false false))).add
    (BinaryFn.const 1)).mul (catalogDegree_binary hn ht ha)).mul
      ((bankSlope_binary hn ht ha).comp pairFst_mem_FP)

theorem fieldOffset_binary : BinaryFn (fieldOffset hn ht ha) :=
  IntegralMixedBankCoordinatePolynomial.massBudget_binary
    (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn false false)
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp pairFst_mem_FP)
    ((bankOffset_binary hn ht ha).comp pairFst_mem_FP)

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

theorem source_mass {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool) (i : ℕ) :
    coefficientMass ((source hn ht ha hR false).polynomial (pair q (BinaryNatCode.encode i))) ≤
      2 ^ (fieldSlope hn ht ha q * R (IntegralMixedPhysicalCriticalQuery.root q) + fieldOffset hn ht ha q) := by
  rw [source_polynomial_catalog]
  have HM := mass_of_bank (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) (catalogArgument n q i) _
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_bank_bounds hn ht ha hR
      (IntegralMixedFramedCoordinateCharacteristicBits.key (catalogArgument n q i)))
  rw [characteristic_count_catalog, characteristic_width_catalog, argument_root_catalog, budget_affine] at HM
  exact HM

theorem derivative_mass {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool) (i k : ℕ) :
    coefficientMass ((derivatives hn ht ha hR false).polynomial
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))) ≤
      2 ^ (fieldSlope hn ht ha q * R (IntegralMixedPhysicalCriticalQuery.root q) + derivativeOffset hn ht ha q) := by
  rw [derivative_polynomial]
  have HB := source_mass hn ht ha hR q i
  have HD : ((source hn ht ha hR false).polynomial (pair q (BinaryNatCode.encode i))).natDegree ≤
      catalogDegree hn ht ha q := by
    have HM := (source hn ht ha hR false).degree_bound (pair q (BinaryNatCode.encode i))
    have HD := degree_catalog hn ht ha hR (pair q []) i
    simp only [degree, pairFst_pair, pairSnd_pair, List.length_replicate] at HD
    rw [HD] at HM
    exact HM
  have HM := IteratedDerivativeBits.mass_bound _ _ _ HD
    (fun j => (coeff_natAbs_le_coefficientMass _ j).trans HB) k
  exact HM.trans (Nat.pow_le_pow_right (by decide) (by
    simp only [derivativeOffset, IteratedDerivativeBits.massBudget]; omega))

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
