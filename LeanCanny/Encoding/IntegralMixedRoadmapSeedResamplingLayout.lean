/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
public import LeanCanny.Encoding.IntegralMixedRoadmapChainConstruction
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
/-! # The concrete depth-zero resampling payload

The candidate is preserved. All record slots, including the reserved final
slot, contain the canonical seed program or its seed padding. Word validity
is checked in the new root; no old word is copied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def payload (d :ℕ):=IntegralMixedRoadmapChain.completePayload d [] (IntegralMixedRoadmapChain.seedCode d)

def packet (d :ℕ) (old w :List Bool):=IntegralMixedRoadmapAtomic.packet (IntegralMixedRoadmapAtomic.candidate old) (payload d) w

theorem candidate_packet (d :ℕ) (old w :List Bool):IntegralMixedRoadmapAtomic.candidate (packet d old w)=IntegralMixedRoadmapAtomic.candidate old:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,pairFst_pair]
theorem original_packet (d :ℕ) (old w :List Bool):IntegralMixedRoadmapAtomic.original (packet d old w)=IntegralMixedRoadmapAtomic.original old:=by
  rw [IntegralMixedRoadmapAtomic.original,candidate_packet]
  rfl
theorem payload_packet (d :ℕ) (old w :List Bool):IntegralMixedRoadmapAtomic.payload (packet d old w)=payload d:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.payload,pairFst_pair,pairSnd_pair]
theorem word_packet (d :ℕ) (old w :List Bool):IntegralMixedRoadmapAtomic.word (packet d old w)=w:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.word,pairSnd_pair]
theorem depth_packet (d :ℕ) (old w :List Bool):IntegralMixedRoadmapAtomic.depth (packet d old w)=0:=by
  simp only [IntegralMixedRoadmapAtomic.depth,payload_packet,payload,IntegralMixedRoadmapChain.depth,IntegralMixedRoadmapChain.completePayload_metadata,
    show WordListRecords.count ([] :List Bool)=0 from WordListRecords.count_encode []]

theorem raw_exact (d :ℕ) :IntegralMixedRoadmapChain.raw (payload d)=WordList.encode
    (IntegralMixedRoadmapChain.seedCodes d++List.replicate (IntegralMixedRoadmapChain.paddingCount d (payload d)+1) (IntegralMixedRoadmapChain.seedCode d)):=by
  change IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapChain.completePayload d [] (IntegralMixedRoadmapChain.seedCode d))=_
  rw [IntegralMixedRoadmapChain.completePayload_raw,IntegralMixedRoadmapChain.compiled,IntegralMixedRoadmapChain.compiledCodes_seed_tail]
  · simp only [IntegralMixedRoadmapChain.meaningfulCodes,IntegralMixedRoadmapChain.depth,IntegralMixedRoadmapChain.completePayload_metadata,
      show WordListRecords.count ([] :List Bool)=0 from WordListRecords.count_encode [],
      List.range_zero,List.flatMap_nil,List.append_nil]
    rfl
  · exact IntegralMixedRoadmapChain.completePayload_probe d [] (IntegralMixedRoadmapChain.seedCode d)

theorem raw_count (d :ℕ) :WordListRecords.count (IntegralMixedRoadmapChain.raw (payload d))=
    IntegralMixedRoadmapRecordChain.probedRecordBound d:=by
  change WordListRecords.count (IntegralMixedRoadmapChain.raw
    (IntegralMixedRoadmapChain.completePayload d [] (IntegralMixedRoadmapChain.seedCode d)))=_
  rw [IntegralMixedRoadmapChain.completePayload_raw,IntegralMixedRoadmapChain.compiled,WordListRecords.count_encode]
  apply IntegralMixedRoadmapChain.compiledCodes_length
  simp only [IntegralMixedRoadmapChain.depth,IntegralMixedRoadmapChain.completePayload_metadata,
    show WordListRecords.count ([] :List Bool)=0 from WordListRecords.count_encode []]
  omega

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem dimension_packet (d :ℕ) (old w :List Bool):
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet d old w)=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.dimension_eq,original_packet]
theorem initial_packet (d :ℕ) (old w :List Bool):
    IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet d old w)=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.initial_eq,IntegralMixedRoadmapAtomic.initial_eq,original_packet]

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width
  IntegralMixedRoadmapAtomic.sourceCap IntegralMixedRoadmapAtomic.scalarBudget

theorem checked (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (w :List Bool) :
    IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old)
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)):=by
  exact IntegralMixedRoadmapChain.complete_seed_checked
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
    (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old) (by
  · have HL :(pairSnd (IntegralMixedRoadmapAtomic.candidate old)).length≤
        IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (IntegralMixedRoadmapAtomic.original old):=hv.2.1.1.1.le
    have HW:=IntegralMixedRoadmapWidth.width_le_scalarBudget hn ht ha (IntegralMixedRoadmapAtomic.original old)
      (pairSnd (IntegralMixedRoadmapAtomic.candidate old))
      (pair (IntegralMixedRoadmapChain.raw (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old))) []) HL
    unfold IntegralMixedRoadmapAtomic.width IntegralMixedPhysicalMarkedPlan.bank
    simp only [Bool.false_eq_true,ite_false,IntegralMixedAuxiliaryMarkedRecordPlan.bank]
    rw [IntegralMixedRoadmapWidth.certified_width]
    simpa only [IntegralMixedRoadmapAtomic.root,candidate_packet,payload_packet,←hv.1.1.2,IntegralMixedRoadmapAtomic.scalarBudget] using HW)
    (IntegralMixedRoadmapAtomic.sourceCap_le hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))

theorem grammar (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)) w) :
    IntegralMixedRoadmapAtomic.Grammar hn ht ha hR0
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w):=by
  have HC:=checked hn ht ha hR0 old hv w
  have HL :(pairSnd (IntegralMixedRoadmapAtomic.candidate old)).length≤
      IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (IntegralMixedRoadmapAtomic.original old):=hv.2.1.1.1.le
  have HP :IntegralMixedRoadmapAtomic.Canonical
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w):=by
    constructor
    · simp only [packet,IntegralMixedRoadmapAtomic.packet,
        IntegralMixedRoadmapAtomic.payload,IntegralMixedRoadmapAtomic.word,IntegralMixedRoadmapAtomic.candidate,
        pairFst_pair,pairSnd_pair]
    · simpa only [candidate_packet,original_packet] using hv.1.1.2
  have HC' :IntegralMixedRoadmapChain.Checked (n (IntegralMixedRoadmapAtomic.original old)+3)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (n (IntegralMixedRoadmapAtomic.original old)+8)
      (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (IntegralMixedRoadmapAtomic.original old))
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)):=by
    simpa only [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.initial_eq,
      IntegralMixedRoadmapAtomic.scalarBudget] using HC
  have HE : (IntegralMixedRoadmapChain.records HC').root
      (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩) (IntegralMixedRoadmapChain.reservedProbe HC')
      (pair (IntegralMixedRoadmapAtomic.original old) (pairSnd (IntegralMixedRoadmapAtomic.candidate old))) []=
      IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w):=by
    simp only [IntegralMixedRoadmapRecordChain.Records.root,←IntegralMixedRoadmapChain.raw_paddedWord HC',
      IntegralMixedRoadmapAtomic.root,payload_packet,candidate_packet,←hv.1.1.2]
  have HW:=IntegralMixedRoadmapWidth.word_length_le_vertexBudget hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.original old) (pairSnd (IntegralMixedRoadmapAtomic.candidate old)) HL
    (IntegralMixedRoadmapChain.records HC') (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩)
    (IntegralMixedRoadmapChain.reservedProbe HC') w (by
      simpa only [IntegralMixedRoadmapWidth.dimension,IntegralMixedRoadmapWidth.initial,HE,
        IntegralMixedRoadmapAtomic.context] using hw)
  refine ⟨HP,?_,?_⟩
  · simpa only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.scalarBudget,original_packet,payload_packet] using HC
  · simpa only [word_packet,IntegralMixedRoadmapAtomic.wordBudget,original_packet] using HW

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
