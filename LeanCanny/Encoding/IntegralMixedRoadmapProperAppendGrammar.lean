/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLayout
/-! # A new own-context sample has the original grammar and word budget -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width IntegralMixedRoadmapAtomic.sourceCap
  IntegralMixedRoadmapAtomic.scalarBudget IntegralMixedRoadmapAtomic.endBirth
  IntegralMixedRoadmapAtomic.frozen IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.payload

theorem grammar (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right)
    (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w)) w):
    IntegralMixedRoadmapAtomic.Grammar hn ht ha hR0
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w):=by
  have HC:=checked hn ht ha hR0 old hv hd left right side hE w
  have HL :(pairSnd (IntegralMixedRoadmapAtomic.candidate old)).length≤
      IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (IntegralMixedRoadmapAtomic.original old):=hv.2.1.1.1.le
  have HP :IntegralMixedRoadmapAtomic.Canonical
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w):=by
    constructor
    · simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.payload,
        IntegralMixedRoadmapAtomic.word,IntegralMixedRoadmapAtomic.candidate,pairFst_pair,pairSnd_pair]
    · simpa only [candidate_packet,original_packet] using hv.1.1.2
  have HC' :IntegralMixedRoadmapChain.Checked (n (IntegralMixedRoadmapAtomic.original old)+3)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w))
      (n (IntegralMixedRoadmapAtomic.original old)+8)
      (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (IntegralMixedRoadmapAtomic.original old))
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side):=by
    simpa only [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.initial_eq,
      IntegralMixedRoadmapAtomic.scalarBudget] using HC
  have HE :(IntegralMixedRoadmapChain.records HC').root (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩)
      (IntegralMixedRoadmapChain.reservedProbe HC')
      (pair (IntegralMixedRoadmapAtomic.original old) (pairSnd (IntegralMixedRoadmapAtomic.candidate old))) []=
      IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old left right side w):=by
    simp only [IntegralMixedRoadmapRecordChain.Records.root,←IntegralMixedRoadmapChain.raw_paddedWord HC',
      IntegralMixedRoadmapAtomic.root,payload_packet,candidate_packet,←hv.1.1.2]
  have HW:=IntegralMixedRoadmapWidth.word_length_le_vertexBudget hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.original old) (pairSnd (IntegralMixedRoadmapAtomic.candidate old)) HL
    (IntegralMixedRoadmapChain.records HC') (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩)
    (IntegralMixedRoadmapChain.reservedProbe HC') w (by
      simpa only [IntegralMixedRoadmapWidth.dimension,IntegralMixedRoadmapWidth.initial,HE,
        IntegralMixedRoadmapAtomic.context] using hw)
  refine ⟨HP,?_,?_⟩
  · simpa only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.scalarBudget,original_packet,
      payload_packet] using HC
  · simpa only [word_packet,IntegralMixedRoadmapAtomic.wordBudget,original_packet] using HW

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
