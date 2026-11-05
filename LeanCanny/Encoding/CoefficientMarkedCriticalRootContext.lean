/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankPhysical
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
/-! # The actual critical query families depend on the prepared ROOT -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalRootContext
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem metadata_aux (P : IntegralCriticalHistoryTask.Parameters)
    (T : IntegralMixedHeaderTablesBits.Tables) (root : List Bool) (m stage : ℕ) (a b : List Bool) :
    CoefficientCriticalCorrelationQuery.nativeMetadata P T (IntegralMixedFramedHistoryFamilyBits.keyAt root m a) stage =
      CoefficientCriticalCorrelationQuery.nativeMetadata P T (IntegralMixedFramedHistoryFamilyBits.keyAt root m b) stage := by
  unfold CoefficientCriticalCorrelationQuery.nativeMetadata
    IntegralMixedFramedCriticalGuardBits.count IntegralMixedFramedCriticalGuardBits.scalar IntegralMixedFramedCriticalGuardBits.physical
    IntegralMixedFramedCriticalGuardBits.scalarPower IntegralMixedFramedCriticalGuardBits.physicalPower
    IntegralMixedFramedCriticalGuardBits.Active IntegralMixedFramedCriticalGuardBits.age IntegralMixedFramedCriticalGuardBits.header
    IntegralMixedFramedCriticalGuardBits.packet IntegralMixedFramedPhysicalIndex.scalarColumn
    IntegralMixedFramedPhysicalIndex.columnPacket IntegralMixedFramedPhysicalIndex.retainedPrefix
    IntegralMixedFramedPhysicalIndex.prefixArity IntegralMixedFramedPhysicalIndex.span
    IntegralMixedFramedHistoryFamilyBits.keyAt IntegralMixedFramedHistoryFamilyBits.prefixLength
    IntegralMixedFullHistoryFamilyBits.prefixLength
  simp only [pairFst_pair, pairSnd_pair, Function.comp_apply]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordBankPolynomial.polynomial CoefficientMarkedRecordBankProducts.common
  CoefficientMarkedRecordBankProducts.cofactor CoefficientMarkedRecordBankDenominator.polynomial

/-- Changing only AUX, including embedding a freshly allocated parent word,
does not change a single constructed full critical query. -/
theorem correlation_aux (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (a b : List Bool) (stage : ℕ) :
    CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha ctx k hk a stage =
      CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha ctx k hk b stage := by
  have hm := metadata_aux (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) ctx
    ((CoefficientMarkedPreludeActual.indices n ctx).length + k) stage a b
  unfold CoefficientMarkedRecordCriticalFullQuery.polynomial CoefficientMarkedRecordCriticalFullQuery.metadata
    CoefficientMarkedRecordCriticalQuery.metadata CoefficientMarkedRecordRowLayout.key
  rw [hm]

private abbrev prefixBirth (ctx : List Bool) (child : Bool) :=
  IntegralMixedPhysicalMarkedPlan.leafCount n false (pair ctx []) + IntegralMixedCausalRecordPlanBits.count ctx -
    (if child then 0 else 1)

private noncomputable def bankFamily (ctx : List Bool) (child : Bool)
    (i : Fin ((CoefficientMarkedPreludeActual.indices n ctx).length +
      (CoefficientMarkedRecordActual.codes ctx (IntegralMixedCausalRecordPlanBits.count ctx - 1)).length)) (k : ℕ) :
    MvPolynomial ℕ ℤ[X] :=
  let selected := min i.val (prefixBirth (n := n) ctx false - 1) + (if child then 1 else 0)
  let stage := IntegralMixedCausalRecordPlanBits.count ctx - (if child then 0 else 1)
  (CoefficientBankUnivariateQuery.polynomial
    (Polynomial.derivative^[k] (CoefficientMarkedRecordBankPolynomial.polynomial hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx - 1) i))
    (2 * FixedWidthPolynomial.count (prefixBirth (n := n) ctx false)
      ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx))
    (UniformIntegralPowerSchedule.birth ((IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx + 1)
      (2 ^ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width ctx)
      (prefixBirth (n := n) ctx child - 1 - selected))
    (CoefficientMarkedRecordBankProducts.cofactor hn ht ha ctx stage selected)
    (CoefficientMarkedRecordBankProducts.common hn ht ha ctx stage)).toMvPolynomial
      (CoefficientMarkedRecordFieldQuery.scalarAt (CoefficientMarkedRecordRows.symbolic hn ht ha ctx stage (Nat.sub_le _ _)) selected)

private theorem bank_factor (q : List Bool) :
    HEq (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) k =>
      CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k)
      (bankFamily hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)) := HEq.rfl

private theorem bankFamily_heq (q r : List Bool) (h : q = r) :
    HEq (bankFamily hn ht ha q) (bankFamily hn ht ha r) := by
  cases h
  rfl

/-- The whole derivative-query family, including its index types, is ROOT
determined. No embedded parent word enters its coefficients or columns. -/
theorem bank_queries_root (q r : List Bool)
    (hroot : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r) :
    HEq (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) k =>
      CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k)
      (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n r)) k =>
        CoefficientMarkedCriticalBankQuery.physical hn ht ha child r i k) :=
  (bank_factor hn ht ha q).trans ((bankFamily_heq hn ht ha _ _ hroot).trans (bank_factor hn ht ha r).symm)

end LeanCanny.Encoding.CoefficientMarkedCriticalRootContext
