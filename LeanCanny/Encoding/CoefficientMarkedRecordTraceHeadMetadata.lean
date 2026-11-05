/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceCutMetadata
/-! # Original-only physical columns of every literal historical head test -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadMetadata
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem column_planned (P : IntegralCriticalHistoryTask.Parameters) (L F C : List Bool → ℕ)
    (T : IntegralMixedHeaderTablesBits.Tables) (q : List Bool) :
    scalarColumn (IntegralMixedFramedNormalizationBits.planned P L F C) T q = scalarColumn P T q := by
  simp only [scalarColumn, columnPacket, retainedPrefix, IntegralMixedFramedHistoryFamilyBits.prefixLength,
    IntegralMixedFullHistoryFamilyBits.prefixLength, prefixArity, span, IntegralMixedFramedNormalizationBits.planned]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def age (b : List Bool) := IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n
  (IntegralFramedTraceCutGuards.root b) - IntegralFramedTraceCutGuards.stage b - 1

noncomputable def column (b : List Bool) := scalarColumn
  (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
  (pair (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n
    (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralFramedTraceCutGuards.root b)))
      (BinaryNatCode.encode (age (n := n) b)))

/-- Every literal stage, including padding, selects an original-only physical
column. No equality of sampler resource functions is asserted. -/
theorem column_eq {R : List Bool → ℕ} (hR : BinaryFn R) (b : List Bool) :
    IntegralMixedPhysicalTraceCutGuards.column hn ht ha hR false b = column hn ht ha b := by
  have hc : IntegralMixedPhysicalReplayNew.count hn ht ha hR false
      (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralFramedTraceCutGuards.root b)) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (IntegralFramedTraceCutGuards.root b) := by
    change (IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n
        (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralFramedTraceCutGuards.root b)))).count = _
    have h := IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha hR
      (IntegralMixedPhysicalMarkedTest.sampleContext (IntegralFramedTraceCutGuards.root b))
    simpa only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair] using h
  unfold IntegralMixedPhysicalTraceCutGuards.column IntegralMixedPhysicalTraceCutGuards.age
  rw [hc, CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR]
  exact column_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha) (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) _ _

end LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadMetadata
