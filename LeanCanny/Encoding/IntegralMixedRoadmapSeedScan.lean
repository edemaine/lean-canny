/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNoCut
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalScanSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # One realized seed point satisfies the actual native scans

The hypotheses are numerical readbacks from one valid full word: every
critical block is the same point, and each creating quotient is its selected
coordinate. Integer prelude stages are inactive; no cut stage is present.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ROOT" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
local notation "CTX" old=>context hn ht ha hR0 old
local notation "N" old=>number n (ROOT old)+8
local notation "K" old=>IntegralMixedCausalRecordPlanBits.count (ROOT old)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.selected
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

structure Readback (old w : List Bool) (hw : SquareSampleCompleteVertices.Valid S ((CTX old)) w)
    (p : Fin ((P).ambient (pairFst ((B).key ((CTX old))))+1)→ℝ) : Prop where
  physical : ∀a, a<(K old)→IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    ((CTX old)) w hw ((N old)+a)=p
  scalar : ∀a, (ha0 : a<(K old))→IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    ((CTX old)) w hw ((N old)+a)=p
      ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ((CTX old)) ((N old)+a),
        IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _
          (critical_active hn ht ha hR0 old a ha0)⟩

theorem readback_retained (old w : List Bool) (hw : SquareSampleCompleteVertices.Valid S ((CTX old)) w)
    (p : Fin ((P).ambient (pairFst ((B).key ((CTX old))))+1)→ℝ)
    (hr : Readback hn ht ha hR0 old w hw p) (a : ℕ) (ha0 : a<(K old))
    (hb : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false ((CTX old)) ((N old)+a)) :
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false ((CTX old)) w hw ((N old)+a) hb=
      p ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ((CTX old)) ((N old)+a),
        IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩ :=by
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    ((CTX old)) w hw ((N old)+a) hb).trans (hr.scalar a ha0)

theorem all_critical_of_readback (old w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S ((CTX old)) w)
    (p : Fin ((P).ambient (pairFst ((B).key ((CTX old))))+1)→ℝ)
    (hr : Readback hn ht ha hR0 old w hw p) :
    pair (ROOT old) w∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false :=by
  apply (IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha (radius_binary hR0) false (ROOT old) w).mpr
  refine ⟨hw,?_⟩
  change ∀b,b<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key ((CTX old)))→
    ∀hb : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false ((CTX old)) b,
      IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false ((CTX old)) w hw b hb=
        IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ((CTX old)) w hw b
          ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ((CTX old)) b,
            IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩
  intro b hb hactive
  rw [prefix_length hn ht ha hR0 old] at hb
  have hN : (N old)≤b :=by
    by_contra h
    exact prelude_inactive hn ht ha hR0 old b (by omega) hactive
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le hN
  have ha0 : a<(K old):=by omega
  rw [hr.physical a ha0]
  exact readback_retained hn ht ha hR0 old w hw p hr a ha0 hactive

theorem seed_count_lower (old : List Bool) :
    IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old+2≤(K old) :=by
  change _≤WordListRecords.count (IntegralMixedCausalRecordPlanBits.records (ROOT old))
  rw [records_root,IntegralMixedRoadmapSeedResampling.raw_exact,WordListRecords.count_encode,
    List.length_append,List.length_replicate,seedCodes_length]
  omega

theorem companion_of_readback (old w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S ((CTX old)) w)
    (p : Fin ((P).ambient (pairFst ((B).key ((CTX old))))+1)→ℝ)
    (hr : Readback hn ht ha hR0 old w hw p) :
    pair (pair ((CTX old)) w) (IntegralMixedPhysicalPointCompanionScan.descriptor ((N old)) ((N old)+1)
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old+1))∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false :=by
  have HK:=seed_count_lower hn ht ha hR0 old
  have HA:=critical_active hn ht ha hR0 old 0 (by omega)
  simp only [Nat.add_zero] at HA
  apply (IntegralMixedPhysicalPointCompanionScan.language_packet_iff hn ht ha (radius_binary hR0) false ((CTX old)) w hw
    ((N old)) ((N old)+1) (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old+1) HA (by
      rw [prefix_length hn ht ha hR0 old]
      omega)).mpr
  intro j hj
  have HJ : 1+j<(K old):=by omega
  have HB:=critical_active hn ht ha hR0 old (1+j) HJ
  have HE : (N old)+1+j=(N old)+(1+j):=by omega
  rw [HE]
  refine ⟨HB,?_,?_⟩
  · rw [hr.physical (1+j) HJ]
    exact (hr.physical 0 (by omega)).symm
  · rw [hr.physical 0 (by omega)]
    exact readback_retained hn ht ha hR0 old w hw p hr (1+j) HJ HB


theorem packet_context (old w : List Bool) :
    IntegralMixedRoadmapAtomic.context (IntegralMixedRoadmapSeedResampling.packet
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=context hn ht ha hR0 old :=by
  simp only [IntegralMixedRoadmapAtomic.context,context,IntegralMixedRoadmapSeedResampling.preparedRoot,
    IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapSeedResampling.candidate_packet,
    IntegralMixedRoadmapSeedResampling.payload_packet]

theorem packet_companion_query (old w : List Bool) :
    IntegralMixedRoadmapAtomic.companionQuery
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=
    pair (pair (CTX old) w) (IntegralMixedPhysicalPointCompanionScan.descriptor (N old) ((N old)+1)
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old+1)) :=by
  let q:=IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w
  have HD:=IntegralMixedRoadmapSeedResampling.dimension_packet hn ht ha hR0
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w
  have HI : IntegralMixedRoadmapAtomic.initial hn ht ha hR0
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)=N old :=by
    rw [IntegralMixedRoadmapSeedResampling.initial_packet hn ht ha hR0,IntegralMixedRoadmapAtomic.initial]
    exact (initial_root hn ht ha hR0 old).symm
  have HZ : IntegralMixedRoadmapAtomic.depth q=0:=IntegralMixedRoadmapSeedResampling.depth_packet _ _ _
  have HA:=IntegralMixedRoadmapAtomic.seed_anchor
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (N old) q HZ
  change IntegralMixedRoadmapAtomic.companionQuery _ _ q=_
  rw [IntegralMixedRoadmapAtomic.companionQuery,HD,HI]
  simp only [IntegralMixedRoadmapAtomic.first,HA,IntegralMixedRoadmapAtomic.free,HZ,Nat.sub_zero]
  rw [IntegralMixedRoadmapAtomic.sampleQuery,packet_context hn ht ha hR0 old w,
    IntegralMixedRoadmapSeedResampling.word_packet]

theorem atomic_companion_of_readback (old w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old) w)
    (p : Fin ((P).ambient (pairFst ((B).key (CTX old)))+1)→ℝ)
    (hr : Readback hn ht ha hR0 old w hw p) :
    IntegralMixedRoadmapAtomic.companionQuery
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0
        (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w))
      (IntegralMixedRoadmapSeedResampling.packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old w)∈
        IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false :=by
  rw [packet_companion_query hn ht ha hR0 old w]
  exact companion_of_readback hn ht ha hR0 old w hw p hr

end LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
