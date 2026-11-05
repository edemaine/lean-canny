/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicControls
/-! # Every own word on a checked atomic table satisfies its original budget -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicWordBudget
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- No target atomic-validity premise is used: the checked table and the
fresh word's own sampler validity suffice for the original word budget. -/
theorem word_bound (candidate payload w : List Bool) {B sourceCap : ℕ}
    (hc : IntegralMixedRoadmapChain.Checked (n (pairFst candidate) + 3) B sourceCap
      (n (pairFst candidate) + 8) (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (pairFst candidate)) payload)
    (hcanonical : candidate = pair (pairFst candidate) (pairSnd candidate))
    (hlabel : (pairSnd candidate).length ≤ IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (pairFst candidate))
    {R : List Bool → ℕ} (hR : BinaryFn R)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext
        (pair candidate (pair (IntegralMixedRoadmapChain.raw payload) []))) w) :
    w.length ≤ IntegralMixedRoadmapWidth.vertexBudget hn ht ha hR (pairFst candidate) := by
  let records := IntegralMixedRoadmapChain.records hc
  let seed := IntegralMixedRoadmapChain.seed (n (pairFst candidate) + 3) (n (pairFst candidate) + 8)
    (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (pairFst candidate)) ⟨0, by omega⟩
  let probe := IntegralMixedRoadmapChain.reservedProbe hc
  have hr : IntegralMixedRoadmapChain.raw payload = records.paddedWord seed probe :=
    IntegralMixedRoadmapChain.raw_paddedWord hc
  apply IntegralMixedRoadmapWidth.word_length_le_vertexBudget hn ht ha hR
    (pairFst candidate) (pairSnd candidate) hlabel records seed probe w
  simpa only [IntegralMixedRoadmapRecordChain.Records.root, ← hr, ← hcanonical,
    IntegralMixedPhysicalMarkedTest.sampleContext] using hw

end LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicWordBudget
