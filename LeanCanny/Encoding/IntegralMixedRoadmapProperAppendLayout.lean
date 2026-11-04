/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicFrame
public import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
public import LeanCanny.Encoding.IntegralMixedChronologicalOptionalEndpointSpec
/-! # Resource and byte provenance of a general chronological level append

Endpoint syntax remains explicit. In particular, a retained right endpoint
must name an old producer even if the left endpoint is fresh.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def payload (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool):=
  IntegralMixedRoadmapChain.appendPayload d (IntegralMixedRoadmapAtomic.payload old)
    l r side (IntegralMixedRoadmapChain.seedCode d)
def packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):=
  IntegralMixedRoadmapAtomic.packet (IntegralMixedRoadmapAtomic.candidate old) (payload d old l r side) w

theorem candidate_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.candidate (packet d old l r side w)=IntegralMixedRoadmapAtomic.candidate old:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,pairFst_pair]
theorem original_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.original (packet d old l r side w)=IntegralMixedRoadmapAtomic.original old:=by
  rw [IntegralMixedRoadmapAtomic.original,candidate_packet]
  rfl
theorem payload_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.payload (packet d old l r side w)=payload d old l r side:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.payload,pairFst_pair,pairSnd_pair]
theorem word_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.word (packet d old l r side w)=w:=by
  simp only [packet,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.word,pairSnd_pair]
theorem depth_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.depth (packet d old l r side w)=IntegralMixedRoadmapAtomic.depth old+1:=by
  simp only [IntegralMixedRoadmapAtomic.depth,payload_packet,payload,IntegralMixedRoadmapChain.append_depth]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

theorem dimension_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet d old l r side w)=
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.dimension_eq,original_packet]
theorem initial_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet d old l r side w)=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old:=by
  rw [IntegralMixedRoadmapAtomic.initial_eq,IntegralMixedRoadmapAtomic.initial_eq,original_packet]

private theorem root_candidate (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root (packet d old l r side w))=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate (IntegralMixedRoadmapAtomic.root old):=by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    pairFst_pair,candidate_packet]

theorem width_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet d old l r side w)=
      IntegralMixedRoadmapAtomic.width hn ht ha hR0 old:=by
  exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 _ _ (root_candidate d old l r side w)

theorem sourceCap_packet (d :ℕ) (old :List Bool) (l r :List Bool) (side :Bool) (w :List Bool):
    IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet d old l r side w)=
      IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old:=by
  unfold IntegralMixedRoadmapAtomic.sourceCap
  congr 1
  · exact congrArg (·+1) (dimension_packet hn ht ha hR0 d old l r side w)
  · exact IntegralMixedMarkedPrefixParameters.degree hn ht ha hR0 _ _ (root_candidate d old l r side w)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.width IntegralMixedRoadmapAtomic.sourceCap
  IntegralMixedRoadmapAtomic.scalarBudget IntegralMixedRoadmapAtomic.endBirth
  IntegralMixedRoadmapAtomic.frozen IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.payload

noncomputable def EndpointsGood (old l r :List Bool):Prop:=
  let d:=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
  let B:=IntegralMixedRoadmapAtomic.width hn ht ha hR0 old
  let cap:=IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old
  let birth:=IntegralMixedRoadmapAtomic.endBirth d (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old
  let labels:=IntegralMixedRoadmapAtomic.frozen old
  IntegralMixedRoadmapEndpointSyntax.Good d B cap birth birth labels l ∧
    IntegralMixedRoadmapEndpointSyntax.Good d B cap birth
      (birth+IntegralMixedRoadmapEndpointSyntax.fresh l) labels r

theorem level_good (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r):
    IntegralMixedRoadmapLevel.Good (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.endBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapAtomic.frozen old) l r side []):=by
  unfold IntegralMixedRoadmapLevel.Good
  simp only [IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
  refine ⟨?_,?_,hE.1,?_,?_,IntegralMixedRoadmapAtomic.sourceCap_le hn ht ha hR0 old,?_⟩
  · exact IntegralMixedRoadmapLevel.frame_mono (IntegralMixedRoadmapAtomic.own_frame_good hn ht ha hR0 old hv)
      (by omega)
  · simpa only [IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,IntegralMixedRoadmapAtomic.frozen_count] using Nat.succ_lt_succ hd
  · simpa only [IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.left,pairFst_pair,pairSnd_pair] using hE.2
  · cases side <;> simp only [IntegralMixedRoadmapLevel.sideWord,pairSnd_pair,pairFst_pair,
      Bool.false_eq_true,ite_false,ite_true]
    all_goals simp
  · cases side <;> simp only [IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.sideWord,
      IntegralMixedRoadmapLevel.slice,pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false,ite_true]
    all_goals rfl

theorem checked (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r)
    (w :List Bool):
    IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old)
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side):=by
  rw [width_packet,sourceCap_packet]
  have HD :IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload old)<
      IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
    simpa only [IntegralMixedRoadmapAtomic.depth] using hd
  have HG:=level_good hn ht ha hR0 old hv hd l r side hE
  simp only [IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.frozen,
    IntegralMixedRoadmapAtomic.depth] at HG
  simpa only [payload] using IntegralMixedRoadmapChain.append_checked
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv) l r side
    (IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)) HD HG
    (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩).property

theorem raw_count (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (l r :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old l r):
    WordListRecords.count (IntegralMixedRoadmapChain.raw
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side))=
    WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload old)):=by
  rw [(checked hn ht ha hR0 old hv hd l r side hE []).2.2.2.2.2.2.1,
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv).2.2.2.2.2.2.1]

theorem prefix_record (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (l r :List Bool) (side :Bool)
    (i :ℕ) (hi :i<IntegralMixedRoadmapChain.rawStart (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
      (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old)):
    WordList.get (IntegralMixedRoadmapChain.raw
      (payload (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old l r side)) i=
      WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload old)) i:=by
  apply IntegralMixedRoadmapChain.append_raw_before (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv)
    l r side (IntegralMixedRoadmapChain.seedCode _) i
  simpa only [IntegralMixedRoadmapAtomic.depth] using hi


end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
