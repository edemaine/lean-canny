/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldPhysical
/-! # Actual radius readers with equal values at the two field roots

No radius functions or their resource certificates are identified. Both bank
product maps are derived under the given reader at their own saved roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedPhysicalFieldEquality (context catalogSelected catalogDegree catalogPower contextProbe)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem radius_full_key (c : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

private theorem radius_certified_snapshot {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR) key =
    IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) key :=
  CoefficientMarkedRecordBankProducts.snapshot_planned _ _ _ _ _ _ key

private theorem radius_context_degree {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
    (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hR).degree (contextProbe n right z k) =
      catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z) := by
  have HD := IntegralMixedPhysicalFieldEquality.degree_catalog hn ht ha hR z
  simpa only [IntegralMixedPhysicalFieldEquality.degree, IntegralMixedPhysicalFieldEquality.derivatives,
    IntegerPolynomialSourceChoice.reindex, IntegerPolynomialIteratedDerivativeBits.source, Function.comp_apply,
    IntegralMixedPhysicalFieldEquality.derivativePacket, contextProbe, pairFst_pair, pairSnd_pair,
    IntegralMixedPhysicalFieldEquality.oldArgument_catalog, CoefficientMarkedRecordFieldSource.root] using HD

private noncomputable def radius_scalars {R : List Bool → ℕ} (hR : BinaryFn R) :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  IntegralMixedFramedBankScalars.scalars B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralFramedPhysicalUnivariateTest.saved B.key)
    (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data B.key
      (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR))

private theorem radius_selected_context {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
    IntegralFramedPhysicalUnivariateTest.selected
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).data
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key
      (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR) (contextProbe n right z k) =
      catalogSelected n right z := by
  simp only [IntegralFramedPhysicalUnivariateTest.selected, IntegralMixedPhysicalFieldEquality.coordinate,
    contextProbe, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [IntegralMixedPhysicalFieldEquality.count_catalog]
  apply min_eq_left
  have HI := IntegralMixedPhysicalFieldEquality.newest_lt
    (IntegralMixedPhysicalFieldEquality.catalogCount n (context right z)) (IntegralMixedPhysicalFieldEquality.label right z)
    (by unfold IntegralMixedPhysicalFieldEquality.catalogCount IntegralMixedAuxiliaryMarkedRecordPlan.fullCount; omega)
  change catalogSelected n right z < IntegralMixedPhysicalFieldEquality.catalogCount n (context right z) at HI
  omega


private theorem radius_scalar_specializes {R : List Bool → ℕ} (hRad : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ R (rightRoot right z)) :
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (catalogSelected n right z)).eval ((2 : ℤ)^ R (rightRoot right z)) =
        (radius_scalars hn ht ha hRad).numerator (contextProbe n right z k) ∧
    (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z))).eval ((2 : ℤ)^ R (rightRoot right z)) =
        (radius_scalars hn ht ha hRad).denominator (contextProbe n right z k) := by
  have HC := CoefficientMarkedRecordBankProducts.cofactor_specializes hn ht ha (rightRoot right z) R
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl [] hR (catalogSelected n right z)
  have HD := CoefficientMarkedRecordBankProducts.common_specializes hn ht ha (rightRoot right z) R
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl [] hR
  rw [show rightRoot right z = pairFst (context right z) from rfl, radius_full_key] at HC HD
  rw [← radius_certified_snapshot hn ht ha hRad] at HC HD
  have HE : IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha hRad := rfl
  constructor
  · simp only [radius_scalars, IntegralMixedFramedBankScalars.scalars]
    rw [radius_selected_context]
    simp only [IntegralFramedPhysicalUnivariateTest.saved, contextProbe, pairFst_pair,
      HE, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    exact HC
  · simp only [radius_scalars, IntegralMixedFramedBankScalars.scalars,
      IntegralFramedPhysicalUnivariateTest.saved, contextProbe, pairFst_pair,
      HE, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    exact HD

theorem specializes_radius {R : List Bool → ℕ} (hRad : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ)
    (hEq : R (CoefficientMarkedRecordFieldSource.root z) = R (rightRoot right z))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z) ≤ R (CoefficientMarkedRecordFieldSource.root z))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ R (rightRoot right z)) :
    (polynomial hn ht ha right z k).map (evalRingHom ((2 : ℤ)^R (CoefficientMarkedRecordFieldSource.root z))) =
      (IntegralMixedPhysicalFieldEquality.querySource hn ht ha hRad).polynomial (contextProbe n right z k) := by
  have HP := CoefficientMarkedRecordFieldSource.derivative_specializes hn ht ha hRad right z hL k
  have HC : (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hRad).polynomial
      (IntegralMixedPhysicalFieldEquality.probe hn ht ha hRad right (pair z (BinaryNatCode.encode k))) =
      (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hRad).polynomial (contextProbe n right z k) := by
    rw [IntegralMixedPhysicalFieldEquality.probe_catalog]
    simp only [IntegralMixedPhysicalFieldEquality.derivatives, IntegerPolynomialSourceChoice.reindex, Function.comp_apply,
      IntegralMixedPhysicalFieldEquality.derivativePacket, contextProbe, IntegralMixedPhysicalFieldEquality.catalogProbe,
      pairFst_pair, pairSnd_pair]
  rw [HC] at HP
  obtain ⟨HA, HB⟩ := radius_scalar_specializes hn ht ha hRad right z k hR
  rw [← hEq] at HA HB
  change (evalRingHom ((2 : ℤ)^ R (CoefficientMarkedRecordFieldSource.root z))) (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (catalogSelected n right z)) = _ at HA
  change (evalRingHom ((2 : ℤ)^ R (CoefficientMarkedRecordFieldSource.root z))) (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z))) = _ at HB
  rw [polynomial, CoefficientBankUnivariateQuery.polynomial_map, HP, HA, HB]
  unfold IntegralMixedPhysicalFieldEquality.querySource IntegralFramedPhysicalUnivariateTest.source
    IntegralMixedFramedBankUnivariateSource.source
  rw [← CoefficientBankUnivariateQuery.polynomial_native, IntegralMixedPhysicalFieldEquality.power_catalog,
    radius_context_degree]
  rfl

theorem physical_specializes_radius {R : List Bool → ℕ} (hRad : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ)
    (hEq : R (CoefficientMarkedRecordFieldSource.root z) = R (rightRoot right z))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z) ≤ R (CoefficientMarkedRecordFieldSource.root z))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ R (rightRoot right z)) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^ R (CoefficientMarkedRecordFieldSource.root z))) (physical hn ht ha right z k) =
      MvPolynomial.rename Fin.val
        (((IntegralMixedPhysicalFieldEquality.querySource hn ht ha hRad).polynomial (contextProbe n right z k)).toMvPolynomial
          (IntegralFramedPhysicalUnivariateTest.column
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false).parameters
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false).plan
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false).data
            (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hRad false).key
            (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hRad) (context right z)
            (pair (IntegralMixedPhysicalFieldEquality.catalogOldArgument n z)
              (pair (BinaryNatCode.encode (catalogSelected n right z)) (BinaryNatCode.encode k))))) := by
  rw [physical, RelativeValueSystemMap.coordinate, specializes_radius hn ht ha hRad right z k hEq hL hR,
    MvPolynomial.rename_toMvPolynomial, column_specializes hn ht ha hRad right z k hR]


end LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
