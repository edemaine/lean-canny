/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNoCritical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityLayout
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointFrame
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalCritical
/-! # The reserved no-critical probe uses the actual checked coarse frame -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "I"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
open IntegralMixedRoadmapProper

private theorem payload_eq (q : List Bool) : IntegralMixedRoadmapAtomic.payload q=
    FormulaSignSlotRadialProviderAtomic.payload q := rfl

private theorem depth_eq (q : List Bool) : IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q := rfl

private theorem bank_ambient (r : List Bool) : (B).parameters.ambient r=
    FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient (FormulaSignSlotRadialProviderRecordPlan.providerContext r) :=by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank
  rfl

private theorem bank_degree (r : List Bool) : (B).parameters.degree r=
    IntegralMixedAuxiliaryMarkedIntegerPlan.degree LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation
      (FormulaSignSlotRadialProviderRecordPlan.providerContext r) :=by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank
  rfl

private theorem latest_lt (q : List Bool) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload q) :=by
  change FormulaSignSlotRadialProviderAtomic.depth q-1<FormulaSignSlotRadialProviderAtomic.depth q
  omega

theorem midpoint_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good (D q) (midBirth (D q) (I q) q) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_anchor
    (IntegralMixedRoadmapChain.level_checked (FormulaSignSlotRadialProviderAtomic.checked q hv.1)
      (levelIndex q) (latest_lt q hd))
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc,payload_eq] using H


theorem midpoint_fit (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    midRawIndex (D q) q<WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)) :=by
  have H:=((FormulaSignSlotRadialProviderAtomic.checked q hv.1).2.2.2.2.1
    (levelIndex q) (latest_lt q hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount at H
  unfold midRawIndex
  rw [payload_eq]
  omega

theorem query_provider (q w : List Bool) :
    pairFst (IntegralMixedPhysicalCriticalQuery.root (query (pair q w)))=
      FormulaSignSlotRadialProviderAtomic.provider q :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.prepare_candidate,
    IntegralMixedPhysicalCriticalQuery.withEndpoints,prefixRoot]

theorem query_dimension (q w : List Bool) :
    (B).parameters.ambient (IntegralMixedPhysicalCriticalQuery.root (query (pair q w)))=D q :=by
  rw [bank_ambient]
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient
    (pairFst (IntegralMixedPhysicalCriticalQuery.root (query (pair q w))))=_
  rw [query_provider,FormulaSignSlotRadialProviderAtomic.dimension_provider]

theorem query_count (q w : List Bool) :
    IntegralMixedCausalRecordPlanBits.count
      (IntegralMixedPhysicalCriticalQuery.root (query (pair q w)))=
        IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1+1 :=by
  simp only [query,IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.prepare_count]
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    IntegralMixedPhysicalCriticalQuery.withEndpoints,prefixRoot,pairFst_pair,pairSnd_pair,
    IntegralMixedRoadmapBadProbePacket.prefixWord,WordListRecords.count_encode,
    IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]

theorem query_birth (q w : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)) :
    FormulaSignSlotRadialProviderCriticalPrefixes.birth false (query (pair q w))=
      I q+IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1 :=by
  unfold FormulaSignSlotRadialProviderCriticalPrefixes.birth FormulaSignSlotRadialProviderRecordPlan.fullCount
  simp only [Bool.false_eq_true,ite_false]
  rw [query_count]
  have HN : FormulaSignSlotRadialProviderRecordPlan.count
      (IntegralMixedPhysicalCriticalQuery.root (query (pair q w)))=I q:=by
    unfold FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderRecordPlan.count
    rw [FormulaSignSlotRadialProviderAtomic.root_provider]
    change FormulaSignSlotRadialProviderIntegerPlan.count
      (pairFst (IntegralMixedPhysicalCriticalQuery.root (query (pair q w))))=_
    rw [query_provider]
  omega

theorem count_positive (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    0<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q) :=by
  have HE : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,payload_eq]
  rw [HE,FormulaSignSlotRadialProviderAtomic.raw_count q hv.1]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem coarse_point_good (q w : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood
      ((B).parameters.ambient (IntegralMixedPhysicalCriticalQuery.root (query (pair q w))))
      (FormulaSignSlotRadialProviderCriticalPrefixes.birth false (query (pair q w)))
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
      (IntegralMixedRoadmapProper.levelIndex q) :=by
  rw [query_dimension,query_birth q w (count_positive q hv)]
  have HG:=FormulaSignSlotRadialProviderProperCritical.midpoint_good q hv hd
  have HI:=FormulaSignSlotRadialProviderProperCritical.midpoint_fit q hv hd
  have HB : IntegralMixedRoadmapProper.midBirth (D q) (I q) q=
      I q+IntegralMixedRoadmapProper.midRawIndex (D q) q:=by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HC : IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload q)):=by
    simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,payload_eq]
  have HL:=IntegralMixedRoadmapProper.labels_count q
  have HD:=FormulaSignSlotRadialProviderAtomic.depth_le q hv.1
  refine ⟨IntegralMixedRoadmapLevel.frame_mono HG.1 ?_,by omega,?_,by omega,?_⟩
  · rw [HB,HC]
    omega
  all_goals unfold IntegralMixedRoadmapProper.levelIndex;rw [depth_eq];omega

local notation "K"=>FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)

theorem query_key_dimension (q w : List Bool) :
    (B).parameters.ambient (pairFst (K (query (pair q w))))=D q :=by
  simpa only [FormulaSignSlotRadialProviderCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    using query_dimension q w

theorem parent_point_good (q w : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood
      ((B).parameters.ambient (pairFst (K (query (pair q w)))))
      ((G).birth (K (query (pair q w))))
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
      (IntegralMixedRoadmapProper.levelIndex q) :=by
  rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false]
  simpa only [FormulaSignSlotRadialProviderCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
    using coarse_point_good q w hv hd

theorem query_packet_key (q w : List Bool) : query (pair q w)=
    IntegralMixedPhysicalCriticalQuery.packet (prefixRoot q)
      (IntegralMixedChronologicalFrameCode.code
        ((B).parameters.ambient (pairFst (K (query (pair q w)))))
        (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
        (IntegralMixedRoadmapProper.levelIndex q)) w
      (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q) :=by
  rw [query_key_dimension]
  simp only [query,code,pairFst_pair,pairSnd_pair]

theorem query_positive (q w : List Bool) : 0<(G).ambient (K (query (pair q w))) :=by
  change 0<(B).parameters.ambient (pairFst (K (query (pair q w))))
  rw [query_key_dimension,FormulaSignSlotRadialProviderIdentity.dimension_eq]
  omega

theorem query_degree (q w : List Bool) :
    ((G).spatial (K (query (pair q w)))).degree=
      BoundedZeroSource.powerDegree
        (LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderAtomic.original q)).toData.size :=by
  change (IntegralMixedFramedHistoryFamilyBits.instruction (B).parameters (B).plan _).source.degree=_
  rw [(B).data.degree_eq]
  rw [bank_degree]
  simp only [FormulaSignSlotRadialProviderCriticalPrefixes.key,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation
      (pairFst (IntegralMixedPhysicalCriticalQuery.root (query (pair q w))))=_
  rw [query_provider]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
