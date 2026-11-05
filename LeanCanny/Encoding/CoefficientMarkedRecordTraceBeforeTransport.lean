/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceStageBinding
/-! # The entire actual before-probe scan keeps one full-row branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceBeforeTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem count_eq {R : List Bool → ℕ} (hR : BinaryFn R) (ctx w : List Bool) :
    IntegralMixedPhysicalTraceCutScan.count hn ht ha hR false (pair ctx w) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  unfold IntegralMixedPhysicalTraceCutScan.count
  change (IntegralMixedFramedBankSnapshotBits.atKey
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n
      (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst (pair ctx w))))).count = _
  rw [IntegralMixedAuxiliaryMarkedRecordPlan.bank_count]
  simp only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair]

/-- This is the whole literal scan, including its actual last-probe exclusion.
Integer prelude commands are handled internally as non-cuts. -/
theorem holds_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ R ctx)
    (hSlarge : CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v)) :
    IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha hR false (pair ctx w) ↔
      IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha hS false (pair ctx w') := by
  unfold IntegralMixedPhysicalTraceBeforeProbe.holds
  rw [count_eq hn ht ha hR ctx w, count_eq hn ht ha hS ctx w']
  apply forall₂_congr
  intro j hj
  by_cases hp : j < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8
  · have hr := CoefficientMarkedRecordTraceStageBinding.prelude_not_cut hn ht ha hR ctx w j hp
    have hs := CoefficientMarkedRecordTraceStageBinding.prelude_not_cut hn ht ha hS ctx w' j hp
    simp only [hr, hs, false_implies]
  · let k := j-(IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8)
    have hk : k < IntegralMixedCausalRecordPlanBits.count ctx := by
      dsimp only [k]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount at hj
      omega
    have hstage : j = CoefficientMarkedRecordCutSource.birth (n := n) ctx k := by
      simp only [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedRecordActual.codes_length,
        CoefficientMarkedPreludeActual.indices_length]
      dsimp only [k]
      omega
    rw [hstage, CoefficientMarkedRecordTraceStageBinding.raw_cut_iff hn ht ha hR ctx w k hk,
      CoefficientMarkedRecordTraceStageBinding.raw_cut_iff hn ht ha hS ctx w' k hk]
    apply forall_congr'
    intro hc
    exact CoefficientMarkedRecordTraceRawGuards.guards_on_curve hn ht ha ctx hR hS hRlarge hSlarge
      ha0 x hx u v hu hv w w' hw hw' hz hz' k hk hc

end LeanCanny.Encoding.CoefficientMarkedRecordTraceBeforeTransport
