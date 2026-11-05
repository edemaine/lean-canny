/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankRadiusHeight

/-! # Affine mass of the actual consecutive-prefix comparison query

The two sides keep their own consecutive physical samplers and power columns.
The source remains the saved parent characteristic, including derivative zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (coordinateSlope coordinateOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

noncomputable def querySource (child : Bool) := IntegralFramedPhysicalUnivariateTest.source
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (IntegralMixedPhysicalCriticalPrefixes.key n false child)
  (coordinate hn ht ha hR false child) (derivatives hn ht ha hR false)

private noncomputable def queryScalars (child : Bool) := IntegralMixedFramedBankScalars.scalars
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (IntegralFramedPhysicalUnivariateTest.saved (IntegralMixedPhysicalCriticalPrefixes.key n false child))
  (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data
    (IntegralMixedPhysicalCriticalPrefixes.key n false child) (coordinate hn ht ha hR false child))

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

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

private theorem scalars_bound (child : Bool) (p : List Bool) :
    (queryScalars hn ht ha hR child |>.numerator p).natAbs ≤
      2 ^ (coordinateSlope hn ht ha (pairFst (pairFst p)) * R (pairFst (pairFst p)) + coordinateOffset hn ht ha (pairFst (pairFst p))) ∧
    (queryScalars hn ht ha hR child |>.denominator p).natAbs ≤
      2 ^ (coordinateSlope hn ht ha (pairFst (pairFst p)) * R (pairFst (pairFst p)) + coordinateOffset hn ht ha (pairFst (pairFst p))) := by
  let A := IntegralMixedFramedBankScalars.scalars (B).parameters (B).plan (B).data
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.seed hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_affine_inputs hn ht ha hR)
    (IntegralFramedPhysicalUnivariateTest.saved (IntegralMixedPhysicalCriticalPrefixes.key n false child))
    (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data
      (IntegralMixedPhysicalCriticalPrefixes.key n false child) (coordinate hn ht ha hR false child))
  have HC := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_coordinate_mass_affine hn ht ha hR
    (IntegralMixedPhysicalCriticalPrefixes.key n false child (pairFst p))
  have HK : pairFst (IntegralMixedPhysicalCriticalPrefixes.key n false child (pairFst p)) = pairFst (pairFst p) := by
    simp only [IntegralMixedPhysicalCriticalPrefixes.key, IntegralMixedFramedHistoryFamilyBits.keyAt,
      IntegralMixedPhysicalCriticalQuery.root, pairFst_pair]
  rw [HK] at HC
  exact ⟨(A.numerator_bound p).trans (Nat.pow_le_pow_right (by decide) HC),
    (A.denominator_bound p).trans (Nat.pow_le_pow_right (by decide) HC)⟩

private theorem context_degree (q : List Bool) (i k : ℕ) :
    (derivatives hn ht ha hR false).degree (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      catalogDegree hn ht ha q := by
  have HD := degree_catalog hn ht ha hR (pair q []) i
  simpa only [degree, derivatives, IntegerPolynomialSourceChoice.reindex, IntegerPolynomialIteratedDerivativeBits.source,
    Function.comp_apply, regroup, pairFst_pair, pairSnd_pair, List.length_replicate] using HD

noncomputable def querySlope (q : List Bool) := fieldSlope hn ht ha q +
  2 * catalogDegree hn ht ha q * coordinateSlope hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
noncomputable def queryOffset (q : List Bool) := derivativeOffset hn ht ha q +
  2 * catalogDegree hn ht ha q * coordinateOffset hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)

theorem querySlope_binary : BinaryFn (querySlope hn ht ha) :=
  (fieldSlope_binary hn ht ha).add (((BinaryFn.const 2).mul (catalogDegree_binary hn ht ha)).mul
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp pairFst_mem_FP))

theorem queryOffset_binary : BinaryFn (queryOffset hn ht ha) :=
  (derivativeOffset_binary hn ht ha).add (((BinaryFn.const 2).mul (catalogDegree_binary hn ht ha)).mul
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp pairFst_mem_FP))

theorem query_mass (child : Bool) (q : List Bool) (i k : ℕ) :
    coefficientMass ((querySource hn ht ha hR child).polynomial
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))) ≤
      2 ^ (querySlope hn ht ha q * R (IntegralMixedPhysicalCriticalQuery.root q) + queryOffset hn ht ha q) := by
  obtain ⟨HN, HD⟩ := scalars_bound hn ht ha hR child (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
  have HM := rational_mass (derivatives hn ht ha hR false) (queryScalars hn ht ha hR child)
    (IntegralMixedFramedBankUnivariateSource.power (B).parameters (B).plan (B).data
      (IntegralFramedPhysicalUnivariateTest.saved (IntegralMixedPhysicalCriticalPrefixes.key n false child))
      (IntegralFramedPhysicalUnivariateTest.selected (B).parameters (B).plan (B).data
        (IntegralMixedPhysicalCriticalPrefixes.key n false child) (coordinate hn ht ha hR false child)))
    (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) _ _
    (derivative_mass hn ht ha hR q i k) HN HD
  rw [context_degree] at HM
  exact HM.trans (Nat.pow_le_pow_right (by decide) (by
    simp only [pairFst_pair, querySlope, queryOffset, IntegralMixedPhysicalCriticalQuery.root]
    exact le_of_eq (by ring)))

theorem physical_query_mass (child : Bool) (q : List Bool) (i k : ℕ) :
    MvMass.mass (((querySource hn ht ha hR child).polynomial
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))).toMvPolynomial
      (IntegralFramedPhysicalUnivariateTest.column (B).parameters (B).plan (B).data
        (IntegralMixedPhysicalCriticalPrefixes.key n false child) (coordinate hn ht ha hR false child) q
        (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))) ≤
      2 ^ (querySlope hn ht ha q * R (IntegralMixedPhysicalCriticalQuery.root q) + queryOffset hn ht ha q) :=
  (DiagonalUnivariateSystem.mass_le _ _).trans (query_mass hn ht ha hR child q i k)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
