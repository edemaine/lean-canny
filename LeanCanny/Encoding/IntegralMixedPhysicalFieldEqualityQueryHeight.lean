/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityRadiusHeight

/-! # Actual positive-cleared field-query mass keeps both source roots

The left root supplies the integer derivative, and the evaluated side supplies
its own bank numerator/common denominator. Their radii are charged separately.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (coordinateSlope coordinateOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

noncomputable def querySource := IntegralFramedPhysicalUnivariateTest.source
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds (B).key
  (coordinate hn ht ha hR) (derivatives hn ht ha hR)

private noncomputable def queryScalars := IntegralMixedFramedBankScalars.scalars
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (IntegralFramedPhysicalUnivariateTest.saved (B).key)
  (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key (coordinate hn ht ha hR))

def contextProbe (n : List Bool → ℕ) (right : Bool) (z : List Bool) (k : ℕ) :=
  pair (context right z) (pair (catalogOldArgument n z)
    (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k)))

private theorem rational_mass (S : IntegerPolynomialRootQueriesBits.Source)
    (A : IntegerPolynomialRationalPointSource.Scalars) (w : List Bool → ℕ) (c : List Bool) (H G : ℕ)
    (hS : coefficientMass (S.polynomial c) ≤ 2 ^ H)
    (ha : (A.numerator c).natAbs ≤ 2 ^ G) (hb : (A.denominator c).natAbs ≤ 2 ^ G) :
    coefficientMass ((IntegerPolynomialRationalPointSource.source S A w).polynomial c) ≤
      2 ^ (H + 2 * S.degree c * G) := by
  have HD : (S.polynomial c).natDegree ≤ 2 * S.degree c := (S.degree_bound c).trans (by omega)
  have HL : coefficientMass (IntegerPolynomialRationalPointSource.linear A c) ≤ 2 ^ G := by
    unfold IntegerPolynomialRationalPointSource.linear
    rw [show (Polynomial.X : ℤ[X]) = Polynomial.X ^ 1 from (pow_one _).symm,
      Polynomial.C_mul_X_pow_eq_monomial, coefficientMass_monomial]
    exact ha
  have HC : coefficientMass (IntegerPolynomialRationalPointSource.constant A c) ≤ 2 ^ G := by
    simpa only [IntegerPolynomialRationalPointSource.constant, coefficientMass_C] using hb
  apply (IntegerPolynomialExpandSource.mass_le _ _).trans
  apply (UnivariateRational.clear_mass _ _ _ _ HD _ HL HC).trans
  exact (Nat.mul_le_mul_right _ hS).trans_eq (by rw [← pow_mul, ← pow_add]; congr 1; ring)

private theorem physical_metadata (r : List Bool) :
    (B).parameters.cap r = (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap r ∧
    (B).parameters.width r = (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width r := by
  simp only [IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,
    IntegralMixedFramedNormalizationBits.planned]
  exact ⟨trivial, trivial⟩

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

private theorem scalars_bound (p : List Bool) :
    (queryScalars hn ht ha hR |>.numerator p).natAbs ≤
      2 ^ (coordinateSlope hn ht ha (pairFst (pairFst p)) * R (pairFst (pairFst p)) + coordinateOffset hn ht ha (pairFst (pairFst p))) ∧
    (queryScalars hn ht ha hR |>.denominator p).natAbs ≤
      2 ^ (coordinateSlope hn ht ha (pairFst (pairFst p)) * R (pairFst (pairFst p)) + coordinateOffset hn ht ha (pairFst (pairFst p))) := by
  let A := IntegralMixedFramedBankScalars.scalars (B).parameters (B).plan (B).data
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_affine_inputs hn ht ha hR)
    (IntegralFramedPhysicalUnivariateTest.saved (B).key)
    (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key (coordinate hn ht ha hR))
  have HC := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_coordinate_mass_affine hn ht ha hR ((B).key (pairFst p))
  have HK : pairFst ((B).key (pairFst p)) = pairFst (pairFst p) := by
    rw [bank_key_catalog]
    simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]
  rw [HK] at HC
  exact ⟨(A.numerator_bound p).trans (Nat.pow_le_pow_right (by decide) HC),
    (A.denominator_bound p).trans (Nat.pow_le_pow_right (by decide) HC)⟩

private theorem context_derivative (right : Bool) (z : List Bool) (k : ℕ) :
    (derivatives hn ht ha hR).polynomial (contextProbe n right z k) =
      (derivatives hn ht ha hR).polynomial (probe hn ht ha hR right (pair z (BinaryNatCode.encode k))) := by
  rw [probe_catalog]
  simp only [derivatives, IntegerPolynomialSourceChoice.reindex, Function.comp_apply, derivativePacket,
    contextProbe, catalogProbe, pairFst_pair, pairSnd_pair]

private theorem context_degree (right : Bool) (z : List Bool) (k : ℕ) :
    (derivatives hn ht ha hR).degree (contextProbe n right z k) = catalogDegree hn ht ha (pairFst (context false z)) := by
  have HD := degree_catalog hn ht ha hR z
  simpa only [degree, derivatives, IntegerPolynomialSourceChoice.reindex, IntegerPolynomialIteratedDerivativeBits.source,
    Function.comp_apply, derivativePacket, contextProbe, pairFst_pair, pairSnd_pair, oldArgument_catalog] using HD

noncomputable def catalogPower (right : Bool) (z : List Bool) :=
  UniformIntegralPowerSchedule.birth
    ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap (pairFst (context right z)) + 1)
    (2 ^ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (pairFst (context right z)))
    (catalogCount n (context right z) - 1 - catalogSelected n right z)

theorem power_catalog (right : Bool) (z : List Bool) (k : ℕ) :
    IntegralMixedFramedBankUnivariateSource.power (B).parameters (B).plan (B).data
      (IntegralFramedPhysicalUnivariateTest.saved (B).key)
      (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key (coordinate hn ht ha hR))
      (contextProbe n right z k) = catalogPower hn ht ha right z := by
  have HS : catalogSelected n right z < catalogCount n (context right z) :=
    newest_lt _ _ (by unfold catalogCount IntegralMixedAuxiliaryMarkedRecordPlan.fullCount; omega)
  have HI : IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key
      (coordinate hn ht ha hR) (contextProbe n right z k) = catalogSelected n right z := by
    simp only [IntegralFramedPhysicalUnivariateTest.selected, coordinate, contextProbe,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [count_catalog]
    exact min_eq_left (by omega)
  have HC : (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data
      ((B).key (context right z))).count = catalogCount n (context right z) := count_catalog hn ht ha hR _
  have HK : pairFst ((B).key (context right z)) = pairFst (context right z) := by
    rw [bank_key_catalog]
    simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, IntegralMixedFramedHistoryFamilyBits.keyAt, pairFst_pair]
  unfold IntegralMixedFramedBankUnivariateSource.power
  rw [HI]
  simp only [IntegralFramedPhysicalUnivariateTest.saved, contextProbe, pairFst_pair]
  rw [HK, HC, (physical_metadata hn ht ha hR _).1, (physical_metadata hn ht ha hR _).2]
  rfl

theorem query_degree_catalog (right : Bool) (z : List Bool) (k : ℕ) :
    (querySource hn ht ha hR).degree (contextProbe n right z k) =
      2 * catalogDegree hn ht ha (pairFst (context false z)) * catalogPower hn ht ha right z := by
  change 2 * (derivatives hn ht ha hR).degree (contextProbe n right z k) *
    IntegralMixedFramedBankUnivariateSource.power (B).parameters (B).plan (B).data
      (IntegralFramedPhysicalUnivariateTest.saved (B).key)
      (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key (coordinate hn ht ha hR))
      (contextProbe n right z k) = _
  rw [context_degree, power_catalog]

noncomputable def queryRightSlope (roots : List Bool) :=
  2 * catalogDegree hn ht ha (pairFst roots) * coordinateSlope hn ht ha (pairSnd roots)
noncomputable def queryOffset (roots : List Bool) :=
  derivativeOffset hn ht ha (pairFst roots) + 2 * catalogDegree hn ht ha (pairFst roots) * coordinateOffset hn ht ha (pairSnd roots)

theorem queryRightSlope_binary : BinaryFn (queryRightSlope hn ht ha) :=
  ((BinaryFn.const 2).mul ((catalogDegree_binary hn ht ha).comp pairFst_mem_FP)).mul
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp pairSnd_mem_FP)

theorem queryOffset_binary : BinaryFn (queryOffset hn ht ha) := by
  have HL : BinaryFn (fun p => derivativeOffset hn ht ha (pairFst p)) :=
    (derivativeOffset_binary hn ht ha).comp pairFst_mem_FP
  have HD : BinaryFn (fun p => catalogDegree hn ht ha (pairFst p)) :=
    (catalogDegree_binary hn ht ha).comp pairFst_mem_FP
  have HR : BinaryFn (fun p => coordinateOffset hn ht ha (pairSnd p)) :=
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp pairSnd_mem_FP
  exact HL.add (((BinaryFn.const 2).mul HD).mul HR)

theorem query_mass (right : Bool) (z : List Bool) (k : ℕ) :
    coefficientMass ((querySource hn ht ha hR).polynomial (contextProbe n right z k)) ≤
      2 ^ (fieldSlope hn ht ha (pairFst (context false z)) * R (pairFst (context false z)) +
        queryRightSlope hn ht ha (pair (pairFst (context false z)) (pairFst (context right z))) * R (pairFst (context right z)) +
        queryOffset hn ht ha (pair (pairFst (context false z)) (pairFst (context right z)))) := by
  have HP := derivative_mass hn ht ha hR right z k
  rw [← context_derivative] at HP
  obtain ⟨HN, HD⟩ := scalars_bound hn ht ha hR (contextProbe n right z k)
  have HM := rational_mass (derivatives hn ht ha hR) (queryScalars hn ht ha hR)
    (IntegralMixedFramedBankUnivariateSource.power (B).parameters (B).plan (B).data
      (IntegralFramedPhysicalUnivariateTest.saved (B).key)
      (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data (B).key (coordinate hn ht ha hR)))
    (contextProbe n right z k) _ _ HP HN HD
  rw [context_degree] at HM
  exact HM.trans (Nat.pow_le_pow_right (by decide) (by
    simp only [contextProbe, pairFst_pair, pairSnd_pair, queryRightSlope, queryOffset]
    exact le_of_eq (by ring)))

theorem physical_query_mass (right : Bool) (z : List Bool) (k : ℕ) :
    MvMass.mass (((querySource hn ht ha hR).polynomial (contextProbe n right z k)).toMvPolynomial
      (IntegralFramedPhysicalUnivariateTest.column (B).parameters (B).plan (B).data (B).key
        (coordinate hn ht ha hR) (context right z)
        (pair (catalogOldArgument n z)
          (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k))))) ≤
      2 ^ (fieldSlope hn ht ha (pairFst (context false z)) * R (pairFst (context false z)) +
        queryRightSlope hn ht ha (pair (pairFst (context false z)) (pairFst (context right z))) * R (pairFst (context right z)) +
        queryOffset hn ht ha (pair (pairFst (context false z)) (pairFst (context right z)))) :=
  (DiagonalUnivariateSystem.mass_le _ _).trans (query_mass hn ht ha hR right z k)

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
