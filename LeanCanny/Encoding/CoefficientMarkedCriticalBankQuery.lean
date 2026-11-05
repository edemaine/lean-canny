/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankSource
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordBankProducts
/-! # The literal consecutive-prefix critical-bank comparison query -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev stage (child : Bool) (q : List Bool) :=
  IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q) - (if child then 0 else 1)

def selected (n : List Bool → ℕ) (child : Bool) (q : List Bool) (i : ℕ) :=
  min i (IntegralMixedPhysicalCriticalPrefixes.birth n false false q - 1) + (if child then 1 else 0)

theorem prefix_key (n : List Bool → ℕ) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) :
    IntegralMixedPhysicalCriticalPrefixes.key n false child q =
      CoefficientMarkedRecordRowLayout.key (n := n) (IntegralMixedPhysicalCriticalQuery.root q) (stage child q) q := by
  cases child
  · exact CoefficientMarkedCriticalBankSource.parent_key n q hc
  · exact CoefficientMarkedCriticalIntervalQuery.child_key n q

private theorem snapshot_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def power (child : Bool) (q : List Bool) (i : ℕ) :=
  UniformIntegralPowerSchedule.birth
    ((parameters hn ht ha).cap (IntegralMixedPhysicalCriticalQuery.root q) + 1)
    (2 ^ (parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q))
    (IntegralMixedPhysicalCriticalPrefixes.birth n false child q - 1 - selected n child q i)

noncomputable def polynomial (child : Bool) (q : List Bool)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) : Polynomial ℤ[X] :=
  CoefficientBankUnivariateQuery.polynomial
    (Polynomial.derivative^[k] (CoefficientMarkedCriticalBankSource.polynomial hn ht ha q i))
    (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) (power hn ht ha child q i.val)
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q) (selected n child q i.val))
    (CoefficientMarkedRecordBankProducts.common hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) (stage child q))

private noncomputable def scalars {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) :=
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  IntegralMixedFramedBankScalars.scalars B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    (IntegralFramedPhysicalUnivariateTest.saved (IntegralMixedPhysicalCriticalPrefixes.key n false child))
    (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data
      (IntegralMixedPhysicalCriticalPrefixes.key n false child)
      (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child))

private theorem physical_metadata {R : List Bool → ℕ} (hR : BinaryFn R) (r : List Bool) :
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.cap r = (parameters hn ht ha).cap r ∧
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters.width r = (parameters hn ht ha).width r := by
  simp only [IntegralMixedPhysicalMarkedPlan.bank, Bool.false_eq_true, ite_false,
    IntegralMixedAuxiliaryMarkedRecordPlan.bank, IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,
    IntegralMixedFramedNormalizationBits.planned]
  exact ⟨trivial, trivial⟩

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedFramedHistoryFamilyBits.family

theorem power_catalog {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool) (i k : ℕ) :
    let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
    IntegralMixedFramedBankUnivariateSource.power B.parameters B.plan B.data
      (IntegralFramedPhysicalUnivariateTest.saved (IntegralMixedPhysicalCriticalPrefixes.key n false child))
      (IntegralFramedPhysicalUnivariateTest.selected B.parameters B.plan B.data
        (IntegralMixedPhysicalCriticalPrefixes.key n false child)
        (IntegralMixedPhysicalCriticalBankEquality.coordinate hn ht ha hR false child))
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = power hn ht ha child q i := by
  dsimp only
  simp only [IntegralMixedFramedBankUnivariateSource.power, IntegralFramedPhysicalUnivariateTest.saved,
    IntegralFramedPhysicalUnivariateTest.selected, pairFst_pair, pairSnd_pair,
    IntegralMixedPhysicalCriticalBankEquality.coordinate, IntegralMixedPhysicalCriticalBankEquality.selected,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [snapshot_count, IntegralMixedPhysicalCriticalPrefixes.key_birth]
  have HK : pairFst (IntegralMixedPhysicalCriticalPrefixes.key n false child q) =
      IntegralMixedPhysicalCriticalQuery.root q := by
    simp only [IntegralMixedPhysicalCriticalPrefixes.key, IntegralMixedFramedHistoryFamilyBits.keyAt,
      pairFst_pair]
  rw [HK, (physical_metadata hn ht ha hR _).1, (physical_metadata hn ht ha hR _).2]
  rfl

private theorem context_degree {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool) (i k : ℕ) :
    (IntegralMixedPhysicalCriticalBankEquality.derivatives hn ht ha hR false).degree
      (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q := by
  have HD := IntegralMixedPhysicalCriticalBankEquality.degree_catalog hn ht ha hR (pair q []) i
  simpa only [IntegralMixedPhysicalCriticalBankEquality.degree, IntegralMixedPhysicalCriticalBankEquality.derivatives,
    IntegerPolynomialSourceChoice.reindex, IntegerPolynomialIteratedDerivativeBits.source,
    Function.comp_apply, IntegralMixedPhysicalCriticalBankEquality.regroup,
    pairFst_pair, pairSnd_pair, List.length_replicate] using HD

private theorem scalar_specializes {R : List Bool → ℕ} (hR : BinaryFn R)
    (child : Bool) (q : List Bool) (i k : ℕ)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q)) :
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q) (selected n child q i)).eval ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)) =
      (scalars hn ht ha hR child).numerator (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) ∧
    (CoefficientMarkedRecordBankProducts.common hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q)).eval ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)) =
      (scalars hn ht ha hR child).denominator (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) := by
  have HC := CoefficientMarkedRecordBankProducts.cofactor_specializes hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) R (stage child q) (Nat.sub_le _ _) q hC (selected n child q i)
  have HD := CoefficientMarkedRecordBankProducts.common_specializes hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) R (stage child q) (Nat.sub_le _ _) q hC
  rw [← prefix_key n child q hc] at HC HD
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  have HS : IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data
      (IntegralMixedPhysicalCriticalPrefixes.key n false child q) =
    IntegralMixedFramedBankSnapshotBits.atKey (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
      (IntegralMixedPhysicalCriticalPrefixes.key n false child q) := by
    exact CoefficientMarkedRecordBankProducts.snapshot_planned (parameters hn ht ha)
      (plan hn ht ha R) (data hn ht ha R) (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (IntegralMixedPhysicalCriticalPrefixes.key n false child q)
  rw [← HS] at HC HD
  constructor
  · simpa only [scalars, IntegralMixedFramedBankScalars.scalars,
      IntegralFramedPhysicalUnivariateTest.saved, IntegralFramedPhysicalUnivariateTest.selected,
      IntegralMixedPhysicalCriticalBankEquality.coordinate, IntegralMixedPhysicalCriticalBankEquality.selected,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, selected] using HC
  · simpa only [scalars, IntegralMixedFramedBankScalars.scalars,
      IntegralFramedPhysicalUnivariateTest.saved, pairFst_pair] using HD

/-- Both probes use the SAME constructed parent characteristic, at their own
prefix denominator, cofactor and fixed creating power. -/
theorem specializes {R : List Bool → ℕ} (hR : BinaryFn R) (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (hC : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (polynomial hn ht ha child q i k).map
      (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q))) =
    (IntegralMixedPhysicalCriticalBankEquality.querySource hn ht ha hR child).polynomial
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) := by
  have HP := CoefficientMarkedCriticalBankSource.derivative_specializes hn ht ha hR q hc hC i k
  obtain ⟨HC, HD⟩ := scalar_specializes hn ht ha hR child q i.val k hc hC
  change (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)))
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q) (selected n child q i.val)) = _ at HC
  change (evalRingHom ((2 : ℤ) ^ R (IntegralMixedPhysicalCriticalQuery.root q)))
    (CoefficientMarkedRecordBankProducts.common hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q)) = _ at HD
  rw [polynomial, CoefficientBankUnivariateQuery.polynomial_map, HP, HC, HD]
  unfold IntegralMixedPhysicalCriticalBankEquality.querySource IntegralFramedPhysicalUnivariateTest.source
    IntegralMixedFramedBankUnivariateSource.source
  rw [← CoefficientBankUnivariateQuery.polynomial_native, power_catalog, context_degree]
  rfl

noncomputable def coefficientBudget (q : List Bool) :=
  IntegerPolynomialDyadic.massBudget
    (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
    (IntegralMixedPhysicalCriticalBankEquality.querySlope hn ht ha q)
    (IntegralMixedPhysicalCriticalBankEquality.queryOffset hn ht ha q)

theorem coefficientBudget_binary : BinaryFn (coefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp pairFst_mem_FP)
    (IntegralMixedPhysicalCriticalBankEquality.querySlope_binary hn ht ha)
    (IntegralMixedPhysicalCriticalBankEquality.queryOffset_binary hn ht ha)

/-- Every derivative order and both independent prepared samplers share one
original parameter-degree/mass budget. -/
theorem coefficient_degree_mass (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k j : ℕ) :
    ((polynomial hn ht ha child q i k).coeff j).natDegree ≤
      IntegralMixedPhysicalCriticalBankEquality.querySlope hn ht ha q ∧
    coefficientMass ((polynomial hn ht ha child q i k).coeff j) ≤ 2 ^ coefficientBudget hn ht ha q := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HS := specializes hn ht ha (BinaryFn.const r) child q hc hr i k
  have HE := congrArg (fun p : ℤ[X] => p.coeff j) HS
  rw [Polynomial.coeff_map] at HE
  change ((polynomial hn ht ha child q i k).coeff j).eval ((2 : ℤ) ^ r) = _ at HE
  rw [HE]
  exact (coeff_natAbs_le_coefficientMass _ j).trans
    (IntegralMixedPhysicalCriticalBankEquality.query_mass hn ht ha (BinaryFn.const r) child q i.val k)

/-- The literal advertised clearing degree is preserved even when a map
kills leading coefficients. -/
theorem target_degree (child : Bool) (q : List Bool)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (polynomial hn ht ha child q i k).natDegree ≤
      (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) * power hn ht ha child q i.val := by
  unfold polynomial CoefficientBankUnivariateQuery.polynomial
  rw [Polynomial.natDegree_expand]
  have HC := UnivariateRational.clear_degree
    (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q)
    (Polynomial.derivative^[k] (CoefficientMarkedCriticalBankSource.polynomial hn ht ha q i))
    (C (CoefficientMarkedRecordBankProducts.cofactor hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (stage child q) (selected n child q i.val)) * X)
    (C (CoefficientMarkedRecordBankProducts.common hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) (stage child q))) 1
    (Polynomial.natDegree_mul_le.trans (by simp)) (by simp)
  exact Nat.mul_le_mul_right _ (by simpa only [Nat.mul_one] using HC)

noncomputable def powerBound (q : List Bool) :=
  UniformIntegralPowerSchedule.birth
    ((parameters hn ht ha).cap (IntegralMixedPhysicalCriticalQuery.root q) + 1)
    (2 ^ (parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q))
    ((parameters hn ht ha).cap (IntegralMixedPhysicalCriticalQuery.root q) + 1)

theorem powerBound_binary : BinaryFn (powerBound hn ht ha) := by
  have HS : UnaryFn (fun q => (parameters hn ht ha).cap (IntegralMixedPhysicalCriticalQuery.root q) + 1) :=
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.comp pairFst_mem_FP).add (UnaryFn.const 1)
  have HN : BinaryFn (fun q => 2 ^ (parameters hn ht ha).width (IntegralMixedPhysicalCriticalQuery.root q)) :=
    (BinaryFn.const 2).powUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width.comp pairFst_mem_FP)
  exact UniformIntegralPowerSchedule.birth_binary HS HN HS

theorem power_le (child : Bool) (q : List Bool) (i : ℕ) : power hn ht ha child q i ≤ powerBound hn ht ha q := by
  unfold power powerBound
  apply UniformIntegralPowerSchedule.birth_le
  have HB := IntegralMixedPhysicalCriticalPrefixes.birth_le hn ht ha (BinaryFn.const 0) false child q
  rw [(physical_metadata hn ht ha (BinaryFn.const 0) _).1] at HB
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans HB)

noncomputable def targetDegree (q : List Bool) :=
  (2 * IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q) * powerBound hn ht ha q

theorem targetDegree_binary : BinaryFn (targetDegree hn ht ha) :=
  ((BinaryFn.const 2).mul (IntegralMixedPhysicalCriticalBankEquality.catalogDegree_binary hn ht ha)).mul
    (powerBound_binary hn ht ha)

/-- One original finite target box covers BOTH probes and ALL derivative orders. -/
theorem target_degree_uniform (child : Bool) (q : List Bool)
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) :
    (polynomial hn ht ha child q i k).natDegree ≤ targetDegree hn ht ha q :=
  (target_degree hn ht ha child q i k).trans (Nat.mul_le_mul_left _ (power_le hn ht ha child q i.val))

end LeanCanny.Encoding.CoefficientMarkedCriticalBankQuery
