/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldSource
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityQueryHeight
/-! # Constructed field-comparison query at a common requested radius

The two roots and their own columns remain independent. A single parameter
specializes both banks at the explicitly common requested radius.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedPhysicalFieldEquality (context catalogSelected catalogDegree catalogPower contextProbe)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def rightRoot (right : Bool) (z : List Bool) := pairFst (context right z)
noncomputable def polynomial (right : Bool) (z : List Bool) (k : ℕ) : Polynomial ℤ[X] :=
  CoefficientBankUnivariateQuery.polynomial
    (Polynomial.derivative^[k] (CoefficientMarkedRecordFieldSource.polynomial hn ht ha z))
    (2 * catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z))
    (catalogPower hn ht ha right z)
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (catalogSelected n right z))
    (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)))

private theorem full_key (c : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

private theorem certified_snapshot {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR) key =
    IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
      (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R) key :=
  CoefficientMarkedRecordBankProducts.snapshot_planned _ _ _ _ _ _ key

private theorem context_degree {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
    (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha hR).degree (contextProbe n right z k) =
      catalogDegree hn ht ha (CoefficientMarkedRecordFieldSource.root z) := by
  have HD := IntegralMixedPhysicalFieldEquality.degree_catalog hn ht ha hR z
  simpa only [IntegralMixedPhysicalFieldEquality.degree, IntegralMixedPhysicalFieldEquality.derivatives,
    IntegerPolynomialSourceChoice.reindex, IntegerPolynomialIteratedDerivativeBits.source, Function.comp_apply,
    IntegralMixedPhysicalFieldEquality.derivativePacket, contextProbe, pairFst_pair, pairSnd_pair,
    IntegralMixedPhysicalFieldEquality.oldArgument_catalog, CoefficientMarkedRecordFieldSource.root] using HD

private noncomputable def scalars {R : List Bool → ℕ} (hR : BinaryFn R) :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  IntegralMixedFramedBankScalars.scalars B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralFramedPhysicalUnivariateTest.saved B.key)
    (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data B.key
      (IntegralMixedPhysicalFieldEquality.coordinate hn ht ha hR))

private theorem selected_context {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z : List Bool) (k : ℕ) :
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

private theorem scalar_specializes (r : ℕ) (right : Bool) (z : List Bool) (k : ℕ)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ r) :
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (catalogSelected n right z)).eval ((2 : ℤ)^r) =
        (scalars hn ht ha (BinaryFn.const r)).numerator (contextProbe n right z k) ∧
    (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot right z))).eval ((2 : ℤ)^r) =
        (scalars hn ht ha (BinaryFn.const r)).denominator (contextProbe n right z k) := by
  have HC := CoefficientMarkedRecordBankProducts.cofactor_specializes hn ht ha (rightRoot right z) (fun _ => r)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl [] hR (catalogSelected n right z)
  have HD := CoefficientMarkedRecordBankProducts.common_specializes hn ht ha (rightRoot right z) (fun _ => r)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) le_rfl [] hR
  rw [show rightRoot right z = pairFst (context right z) from rfl, full_key] at HC HD
  rw [← certified_snapshot hn ht ha (BinaryFn.const r)] at HC HD
  have HE : IntegralMixedPhysicalMarkedPlan.bank hn ht ha (BinaryFn.const r) false =
      IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (BinaryFn.const r) := rfl
  constructor
  · simp only [scalars, IntegralMixedFramedBankScalars.scalars]
    rw [selected_context]
    simp only [IntegralFramedPhysicalUnivariateTest.saved, contextProbe, pairFst_pair,
      HE, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    exact HC
  · simp only [scalars, IntegralMixedFramedBankScalars.scalars,
      IntegralFramedPhysicalUnivariateTest.saved, contextProbe, pairFst_pair,
      HE, IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    exact HD

theorem specializes (r : ℕ) (right : Bool) (z : List Bool) (k : ℕ)
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (CoefficientMarkedRecordFieldSource.root z) ≤ r)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot right z) ≤ r) :
    (polynomial hn ht ha right z k).map (evalRingHom ((2 : ℤ)^r)) =
      (IntegralMixedPhysicalFieldEquality.querySource hn ht ha (BinaryFn.const r)).polynomial (contextProbe n right z k) := by
  have HP := CoefficientMarkedRecordFieldSource.derivative_specializes hn ht ha (BinaryFn.const r) right z hL k
  have HC : (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha (BinaryFn.const r)).polynomial
      (IntegralMixedPhysicalFieldEquality.probe hn ht ha (BinaryFn.const r) right (pair z (BinaryNatCode.encode k))) =
      (IntegralMixedPhysicalFieldEquality.derivatives hn ht ha (BinaryFn.const r)).polynomial (contextProbe n right z k) := by
    rw [IntegralMixedPhysicalFieldEquality.probe_catalog]
    simp only [IntegralMixedPhysicalFieldEquality.derivatives, IntegerPolynomialSourceChoice.reindex, Function.comp_apply,
      IntegralMixedPhysicalFieldEquality.derivativePacket, contextProbe, IntegralMixedPhysicalFieldEquality.catalogProbe,
      pairFst_pair, pairSnd_pair]
  rw [HC] at HP
  obtain ⟨HA, HB⟩ := scalar_specializes hn ht ha r right z k hR
  change (evalRingHom ((2 : ℤ)^r)) (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z)) (catalogSelected n right z)) = _ at HA
  change (evalRingHom ((2 : ℤ)^r)) (CoefficientMarkedRecordBankProducts.common hn ht ha (rightRoot right z)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot right z))) = _ at HB
  rw [polynomial, CoefficientBankUnivariateQuery.polynomial_map, HP, HA, HB]
  unfold IntegralMixedPhysicalFieldEquality.querySource IntegralFramedPhysicalUnivariateTest.source
    IntegralMixedFramedBankUnivariateSource.source
  rw [← CoefficientBankUnivariateQuery.polynomial_native, IntegralMixedPhysicalFieldEquality.power_catalog,
    context_degree]
  rfl

end LeanCanny.Encoding.CoefficientMarkedRecordFieldQuery
