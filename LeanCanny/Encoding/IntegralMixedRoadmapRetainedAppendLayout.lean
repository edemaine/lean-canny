/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicFrame
public import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
public import LeanCanny.Encoding.IntegralMixedChronologicalOptionalEndpointSpec
/-! # A concrete equal-retained-endpoint extension of an accepted history

The endpoint is an old chronological producer. All endpoint syntax, original
widths and code budgets are derived. This file proves syntax and resource
provenance only; a new full word is checked in its own appended root.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def endpoint (producer :ℕ):=IntegralMixedRoadmapEndpointSyntax.spec 0 producer 0 0 0 0
def payload (d :ℕ) (old :List Bool) (producer :ℕ):=
  IntegralMixedRoadmapChain.appendPayload d (IntegralMixedRoadmapAtomic.payload old)
    (endpoint producer) (endpoint producer) false (IntegralMixedRoadmapChain.seedCode d)
def packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):=
  IntegralMixedRoadmapAtomic.packet (IntegralMixedRoadmapAtomic.candidate old) (payload d old producer) w

theorem candidate_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.candidate (packet d old producer w)=IntegralMixedRoadmapAtomic.candidate old:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,pairFst_pair]
theorem original_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.original (packet d old producer w)=IntegralMixedRoadmapAtomic.original old:=by
  rw [IntegralMixedRoadmapAtomic.original,candidate_packet]
  rfl
theorem payload_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.payload (packet d old producer w)=payload d old producer:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.payload,pairFst_pair,pairSnd_pair]
theorem word_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.word (packet d old producer w)=w:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.word,pairSnd_pair]
theorem depth_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.depth (packet d old producer w)=IntegralMixedRoadmapAtomic.depth old+1:=by
  simp only [IntegralMixedRoadmapAtomic.depth,payload_packet,payload,IntegralMixedRoadmapChain.append_depth]

theorem endpoint_good (d B sourceCap birth current producer :ℕ) (labels :List Bool) (he :producer<birth):
    IntegralMixedRoadmapEndpointSyntax.Good d B sourceCap birth current labels (endpoint producer):=by
  refine ⟨(IntegralMixedRoadmapEndpointSyntax.canonical_spec _ _ _ _ _ _).symm,Or.inl ?_⟩
  simpa only [endpoint,IntegralMixedRoadmapEndpointSyntax.field_spec_0,
    IntegralMixedRoadmapEndpointSyntax.field_spec_1,IntegralMixedRoadmapEndpointSyntax.field_spec_2,
    IntegralMixedRoadmapEndpointSyntax.field_spec_3,IntegralMixedRoadmapEndpointSyntax.field_spec_4,
    IntegralMixedRoadmapEndpointSyntax.field_spec_5,eq_self_iff_true,true_and,and_true] using he

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem dimension_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet d old producer w)=
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.dimension_eq,original_packet]
theorem initial_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet d old producer w)=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.initial_eq,IntegralMixedRoadmapAtomic.initial_eq,original_packet]

private theorem root_candidate (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root (packet d old producer w))=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root old):=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    pairFst_pair,candidate_packet]

theorem width_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet d old producer w)=
      IntegralMixedRoadmapAtomic.width hn ht ha hR0 old:=by
  exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 _ _ (root_candidate d old producer w)

theorem sourceCap_packet (d :ℕ) (old :List Bool) (producer :ℕ) (w :List Bool):
    IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet d old producer w)=
      IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old:=by
  unfold IntegralMixedRoadmapAtomic.sourceCap
  congr 1
  · exact congrArg (·+1) (dimension_packet hn ht ha hR0 d old producer w)
  · exact IntegralMixedMarkedPrefixParameters.degree hn ht ha hR0 _ _ (root_candidate d old producer w)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width IntegralMixedRoadmapAtomic.sourceCap
  IntegralMixedRoadmapAtomic.scalarBudget IntegralMixedRoadmapAtomic.endBirth
  IntegralMixedRoadmapAtomic.frozen IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.payload

theorem level_good (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    IntegralMixedRoadmapLevel.Good (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.endBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old)
        (endpoint producer) (endpoint producer) false []):=by
  unfold IntegralMixedRoadmapLevel.Good
  simp only [IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
  refine ⟨?_,?_,?_,?_,?_,IntegralMixedRoadmapAtomic.sourceCap_le hn ht ha hR0 old,?_⟩
  · exact IntegralMixedRoadmapLevel.frame_mono (IntegralMixedRoadmapAtomic.own_frame_good hn ht ha hR0 old hv)
      (by omega)
  · simpa only [IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,IntegralMixedRoadmapAtomic.frozen_count] using Nat.succ_lt_succ hd
  · exact endpoint_good _ _ _ _ _ _ _ he
  · exact endpoint_good _ _ _ _ _ _ _ he
  · left
    simp only [IntegralMixedRoadmapLevel.sideWord,pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false]
  · have HN :decide (([] :List Bool)=[true])=false:=rfl
    simp only [IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.sideWord,
      IntegralMixedRoadmapLevel.slice,pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false,
      HN]

theorem checked (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
    (w :List Bool):
    IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old)
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer):=by
  rw [width_packet,sourceCap_packet]
  have HD :IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload old)<
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
    simpa only [IntegralMixedRoadmapAtomic.depth] using hd
  have HG:=level_good hn ht ha hR0 old hv hd producer he
  simp only [IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.frozen,
    IntegralMixedRoadmapAtomic.depth] at HG
  simpa only [payload] using IntegralMixedRoadmapChain.append_checked
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv) (endpoint producer) (endpoint producer) false
    (IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)) HD HG
    (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩).property

theorem raw_count (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    WordListRecords.count (IntegralMixedRoadmapChain.raw
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer))=
    WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload old)):=by
  rw [(checked hn ht ha hR0 old hv hd producer he []).2.2.2.2.2.2.1,
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv).2.2.2.2.2.2.1]

theorem prefix_record (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (producer :ℕ)
    (i :ℕ) (hi :i<IntegralMixedRoadmapChain.rawStart (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old)):
    WordList.get (IntegralMixedRoadmapChain.raw
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer)) i=
      WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload old)) i:=by
  apply IntegralMixedRoadmapChain.append_raw_before (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv)
    (endpoint producer) (endpoint producer) false (IntegralMixedRoadmapChain.seedCode _) i
  simpa only [IntegralMixedRoadmapAtomic.depth] using hi

theorem grammar (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
    (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w)) w):
    IntegralMixedRoadmapAtomic.Grammar hn ht ha hR0
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w):=by
  have HC:=checked hn ht ha hR0 old hv hd producer he w
  have HL :(pairSnd (IntegralMixedRoadmapAtomic.candidate old)).length≤
      IntegralMixedAuxiliaryCandidate.labelWidth hn ht ha (IntegralMixedRoadmapAtomic.original old):=hv.2.1.1.1.le
  have HP :IntegralMixedRoadmapAtomic.Canonical
      (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w):=by
    constructor
    · simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.payload,
        IntegralMixedRoadmapAtomic.word,IntegralMixedRoadmapAtomic.candidate,pairFst_pair,pairSnd_pair]
    · simpa only [candidate_packet,original_packet] using hv.1.1.2
  have HC' :IntegralMixedRoadmapChain.Checked (n (IntegralMixedRoadmapAtomic.original old)+3)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0
        (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w))
      (n (IntegralMixedRoadmapAtomic.original old)+8)
      (IntegralMixedRoadmapWidth.scalarBudget hn ht ha (IntegralMixedRoadmapAtomic.original old))
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer):=by
    simpa only [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.initial_eq,
      IntegralMixedRoadmapAtomic.scalarBudget] using HC
  have HE :(IntegralMixedRoadmapChain.records HC').root (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩)
      (IntegralMixedRoadmapChain.reservedProbe HC')
      (pair (IntegralMixedRoadmapAtomic.original old) (pairSnd (IntegralMixedRoadmapAtomic.candidate old))) []=
      IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old producer w):=by
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

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
