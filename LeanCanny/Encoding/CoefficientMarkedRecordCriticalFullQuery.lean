/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalDegree
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBounds
/-! # Actual critical queries in the literal symbolic full-row variable space

The count equality is derived from actual headers and actual indexed layout.
No caller supplies a column, count, header or polynomial presentation.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem native_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (key : List Bool) (stage : ℕ) :
    (CoefficientCriticalCorrelationQuery.nativeMetadata P T key stage).count = IntegralFramedPhysicalSquare.count P D key :=
  IntegralMixedFramedCriticalGuardBits.count_actual P D H T hr (fun _ => key) []

private theorem planned_count (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralFramedPhysicalSquare.count (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) key = IntegralFramedPhysicalSquare.count P D key := rfl

private theorem with_count (M : CoefficientCriticalCorrelationQuery.Metadata) (N : ℕ) (h : N = M.count) :
    {M with count := N} = M := by
  cases h
  rfl

private theorem polynomial_map_heq {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (M N : CoefficientCriticalCorrelationQuery.Metadata) (h : M = N) (d : R) :
    HEq (MvPolynomial.map φ (CoefficientCriticalCorrelationQuery.polynomial M d))
      (MvPolynomial.map φ (CoefficientCriticalCorrelationQuery.polynomial N d)) := by
  cases h
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem symbolic_count (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count =
      (CoefficientMarkedRecordRowLayout.fixed hn ht ha ctx k hk).count := rfl

theorem count_eq (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) :
    (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).count =
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count := by
  have hm := congrArg CoefficientCriticalCorrelationQuery.Metadata.count
    (CoefficientMarkedRecordCriticalQuery.metadata_eq hn ht ha ctx (BinaryFn.const 0) k aux stage)
  have hc := native_count
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (BinaryFn.const 0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (BinaryFn.const 0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (BinaryFn.const 0))
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha (BinaryFn.const 0) false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (BinaryFn.const 0) false)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) stage
  have hp := planned_count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha (fun _ => 0)) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (BinaryFn.const 0))
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
  exact hm.trans (hc.trans (hp.trans ((CoefficientMarkedRecordRowLayout.count_eq hn ht ha ctx (fun _ => 0) k hk aux).trans
    (symbolic_count hn ht ha ctx k hk).symm)))

noncomputable def metadata (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) : CoefficientCriticalCorrelationQuery.Metadata :=
  {CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage with
    count := (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count}

theorem metadata_eq (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) : metadata hn ht ha ctx k hk aux stage =
      CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage :=
  with_count _ _ (count_eq hn ht ha ctx k hk aux stage).symm

noncomputable def polynomial (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) : MvPolynomial (Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count) ℤ[X] :=
  CoefficientCriticalCorrelationQuery.polynomial (metadata hn ht ha ctx k hk aux stage)
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k
      (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).age)

attribute [local irreducible] metadata polynomial CoefficientMarkedRecordRows.symbolic
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedSourceIntegerRecordAppend.plan

theorem specializes (ctx : List Bool) {R : List Bool → ℕ} (hR : BinaryFn R) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) (stage : ℕ)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx)) (polynomial hn ht ha ctx k hk aux stage))
      (IntegralMixedFramedCriticalGuardBits.polynomial
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (fun _ => CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) (fun _ => stage) []) := by
  have hm := polynomial_map_heq (evalRingHom ((2 : ℤ)^R ctx)) _ _ (metadata_eq hn ht ha ctx k hk aux stage)
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k
      (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).age)
  have hs := CoefficientMarkedRecordCriticalQuery.specializes hn ht ha ctx hR k hk aux stage hlarge
  unfold polynomial metadata CoefficientMarkedRecordCriticalQuery.polynomial at *
  exact hm.trans hs

theorem polynomial_degree (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) : (polynomial hn ht ha ctx k hk aux stage).totalDegree ≤
      CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx := by
  have hh := CoefficientCriticalCorrelationQuery.native_count_degree
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) stage
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k
      (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).age)
  unfold polynomial metadata CoefficientMarkedRecordCriticalQuery.metadata at *
  simpa only [CoefficientMarkedRecordRowLayout.key_root, CoefficientMarkedRecordRowDegree.spatialDegree] using hh

theorem coefficient_degree_mass (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (aux : List Bool) (stage : ℕ) (e : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count →₀ ℕ) :
    ((polynomial hn ht ha ctx k hk aux stage).coeff e).natDegree ≤ IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx ∧
      coefficientMass ((polynomial hn ht ha ctx k hk aux stage).coeff e) ≤
        2 ^ CoefficientMarkedRecordCriticalQuery.coefficientBudget hn ht ha ctx := by
  obtain ⟨hd, hm⟩ := CoefficientMarkedRecordBankDenominator.degree_mass hn ht ha ctx k hk
    (CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage).age
  unfold polynomial metadata
  exact CoefficientCriticalCorrelationQuery.coefficient_degree_mass
    {CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx k aux stage with
      count := (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count} _ _ _ hd hm e

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
