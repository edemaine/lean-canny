/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCritical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical
/-! # The reserved no-critical probe uses the actual checked coarse frame -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem query_candidate (q w : List Bool) :
    pairFst (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w)))=
      IntegralMixedRoadmapAtomic.candidate q :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.prepare_candidate,
    IntegralMixedPhysicalCriticalQuery.withEndpoints,prefixRoot]

theorem query_dimension (q w : List Bool) :
    (B).parameters.ambient (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w)))=D q :=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n
    (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w)))+3=_
  rw [IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0]
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,
    IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
    query_candidate,IntegralMixedRoadmapAtomic.original]

theorem query_count (q w : List Bool) :
    IntegralMixedCausalRecordPlanBits.count
      (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w)))=
        IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1+1 :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.prepare_count]
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    IntegralMixedPhysicalCriticalQuery.withEndpoints,prefixRoot,pairFst_pair,pairSnd_pair,
    IntegralMixedRoadmapBadProbePacket.prefixWord,WordListRecords.count_encode,
    IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]

theorem query_birth (q w : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)) :
    IntegralMixedPhysicalCriticalPrefixes.birth n false false (query hn ht ha hR0 (pair q w))=
      I q+IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1 :=by
  unfold IntegralMixedPhysicalCriticalPrefixes.birth IntegralMixedPhysicalMarkedPlan.leafCount
  simp only [pairFst_pair,Bool.false_eq_true,ite_false]
  rw [query_count]
  have HN : IntegralMixedAuxiliaryMarkedIntegerSource.number n
      (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w)))+8=I q:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,
      IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      query_candidate,IntegralMixedRoadmapAtomic.original]
  omega

theorem count_positive (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    0<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q) :=by
  have HE : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  rw [HE,IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 q hv]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem coarse_point_good (q w : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood
      ((B).parameters.ambient (IntegralMixedPhysicalCriticalQuery.root (query hn ht ha hR0 (pair q w))))
      (IntegralMixedPhysicalCriticalPrefixes.birth n false false (query hn ht ha hR0 (pair q w)))
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
      (IntegralMixedRoadmapProper.levelIndex q) :=by
  rw [query_dimension,query_birth hn ht ha hR0 q w (count_positive hn ht ha hR0 q hv)]
  have HG:=IntegralMixedRoadmapProper.midpoint_good hn ht ha hR0 q hv hd
  have HI:=IntegralMixedRoadmapProper.midpoint_fit hn ht ha hR0 q hv hd
  have HB : IntegralMixedRoadmapProper.midBirth (D q) (I q) q=
      I q+IntegralMixedRoadmapProper.midRawIndex (D q) q:=by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HC : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  have HL:=IntegralMixedRoadmapProper.labels_count q
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  refine ⟨IntegralMixedRoadmapLevel.frame_mono HG.1 ?_,by omega,?_,by omega,?_⟩
  · rw [HB,HC]
    omega
  all_goals unfold IntegralMixedRoadmapProper.levelIndex;omega

local notation "K"=>IntegralMixedPhysicalCriticalPrefixes.key n false false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)

theorem query_key_dimension (q w : List Bool) :
    (B).parameters.ambient (pairFst (K (query hn ht ha hR0 (pair q w))))=D q :=by
  simpa only [IntegralMixedPhysicalCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    using query_dimension hn ht ha hR0 q w

theorem parent_point_good (q w : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood
      ((B).parameters.ambient (pairFst (K (query hn ht ha hR0 (pair q w)))))
      ((G).birth (K (query hn ht ha hR0 (pair q w))))
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
      (IntegralMixedRoadmapProper.levelIndex q) :=by
  rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha (radius_binary hR0) false false]
  simpa only [IntegralMixedPhysicalCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    using coarse_point_good hn ht ha hR0 q w hv hd

theorem query_packet_key (q w : List Bool) : query hn ht ha hR0 (pair q w)=
    IntegralMixedPhysicalCriticalQuery.packet (prefixRoot q)
      (IntegralMixedChronologicalFrameCode.code
        ((B).parameters.ambient (pairFst (K (query hn ht ha hR0 (pair q w)))))
        (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
        (IntegralMixedRoadmapProper.levelIndex q)) w
      (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q) :=by
  rw [query_key_dimension]
  simp only [query,code,pairFst_pair,pairSnd_pair]

theorem query_positive (q w : List Bool) : 0<(G).ambient (K (query hn ht ha hR0 (pair q w))) :=by
  change 0<(B).parameters.ambient (pairFst (K (query hn ht ha hR0 (pair q w))))
  rw [query_key_dimension,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0]
  omega

theorem query_degree (q w : List Bool) :
    ((G).spatial (K (query hn ht ha hR0 (pair q w)))).degree=
      BoundedZeroSource.powerDegree (t (IntegralMixedRoadmapAtomic.original q)).toData.size :=by
  change (IntegralMixedFramedHistoryFamilyBits.instruction (B).parameters (B).plan _).source.degree=_
  rw [(B).data.degree_eq]
  unfold IntegralMixedPhysicalMarkedPlan.bank
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree t
    (pairFst (K (query hn ht ha hR0 (pair q w))))=_
  simp only [IntegralMixedAuxiliaryMarkedIntegerPlan.degree,IntegralMixedPhysicalCriticalPrefixes.key,
    IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair,
    IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
    query_candidate,IntegralMixedRoadmapAtomic.original]

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
