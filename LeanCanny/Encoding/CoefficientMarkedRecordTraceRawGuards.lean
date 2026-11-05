/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceHeadSign
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceGuardMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceProbeSign
public import LeanCanny.Computation.FiniteCoefficientGuardTransport
/-! # Whole actual historical raw-cut guards on one complete root branch -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceRawGuards
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem query_packet (ctx w : List Bool) (j e k : ℕ) :
    IntegralMixedPhysicalTraceCutGuards.query (FiniteCoefficientSignScan.query
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) e k) =
    pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
      (IntegralFramedPhysicalTraceCutSource.datum (List.replicate j true) e k) := by
  simp only [IntegralMixedPhysicalTraceCutGuards.query, FiniteCoefficientSignScan.query,
    IntegralFramedTraceCutScan.stagePacket, IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutGuards.word, IntegralFramedPhysicalTraceCutSource.datum, pairFst_pair, pairSnd_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- All lower, leading, higher and head/constant clauses are transported
SIMULTANEOUSLY on the same own full words. No guard is supplied as a premise. -/
theorem guards_on_curve (ctx : List Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
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
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w' hw').val (x v))
    (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR false
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ↔
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hS false
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w') (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) := by
  apply FiniteCoefficientGuardTransport.guards_iff
  · rw [CoefficientMarkedRecordTraceCutMetadata.choice hn ht ha hR ctx w k hk,
      CoefficientMarkedRecordTraceCutMetadata.choice hn ht ha hS ctx w' k hk]
  · rw [CoefficientMarkedRecordTraceCutMetadata.degree hn ht ha hR ctx w k hk,
      CoefficientMarkedRecordTraceCutMetadata.degree hn ht ha hS ctx w' k hk]
  · rw [CoefficientMarkedRecordTraceGuardMetadata.cap_eq hn ht ha hR,
      CoefficientMarkedRecordTraceGuardMetadata.cap_eq hn ht ha hS]
  · rw [CoefficientMarkedRecordTraceCutMetadata.degree hn ht ha hR ctx w k hk,
      CoefficientMarkedRecordTraceGuardMetadata.cap_eq hn ht ha hR]
    exact (CoefficientMarkedRecordTraceGuardMetadata.header_bounds hn ht ha ctx k).2
  · intro e he requested hrequested
    rw [CoefficientMarkedRecordTraceGuardMetadata.cap_eq hn ht ha hR] at he
    rw [CoefficientMarkedRecordTraceCutMetadata.choice hn ht ha hR ctx w k hk] at hrequested
    have hr := hrequested.trans (CoefficientMarkedRecordTraceGuardMetadata.header_bounds hn ht ha ctx k).1
    unfold IntegralMixedPhysicalTraceCutGuards.sign
    simp only [Function.comp_apply, query_packet]
    exact CoefficientMarkedRecordTraceProbeSign.value_on_curve hn ht ha ctx hR hS hRlarge hSlarge
      ha0 x hx u v hu hv [] [] w w' hw hw' hz hz' ⟨k, hk, hc, requested, e⟩ he hr
  · exact CoefficientMarkedRecordTraceHeadSign.value_on_curve hn ht ha ctx hR hS ha0 x hx u v w w' hw hw' hz hz'
      (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)

end LeanCanny.Encoding.CoefficientMarkedRecordTraceRawGuards
