/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
public import LeanCanny.Encoding.IntegralMixedRoadmapProperInputComposition
/-! # Accepted row witnesses preserve every actual older retained value -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

private theorem scan_sound (cL wL cR wR table : List Bool)
    (H : IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR table∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)) :
    ∃hL : SquareSampleCompleteVertices.Valid S cL wL,∃hR : SquareSampleCompleteVertices.Valid S cR wR,
      ∀i<WordListRecords.count table,
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) cL wL hL
          (IntegralMixedPhysicalFieldEqualityList.label false (WordList.get table i))=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) cR wR hR
          (IntegralMixedPhysicalFieldEqualityList.label true (WordList.get table i)) :=by
  have HL : SquareSampleCompleteVertices.Valid S cL wL:=by
    simpa only [IntegralMixedPhysicalFieldEquality.context,IntegralMixedPhysicalFieldEquality.word,
      IntegralMixedPhysicalFieldEquality.sample,IntegralMixedPhysicalFieldEqualityList.packet,
      Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using H.1
  have HR : SquareSampleCompleteVertices.Valid S cR wR:=by
    simpa only [IntegralMixedPhysicalFieldEquality.context,IntegralMixedPhysicalFieldEquality.word,
      IntegralMixedPhysicalFieldEquality.sample,IntegralMixedPhysicalFieldEqualityList.packet,
      ite_true,pairFst_pair,pairSnd_pair] using H.2.1
  refine ⟨HL,HR,fun i hi=>?_⟩
  have HI:=H.2.2 i (by simpa only [IntegralMixedPhysicalFieldEqualityList.count,
    IntegralMixedPhysicalFieldEqualityList.table,IntegralMixedPhysicalFieldEqualityList.packet,pairSnd_pair] using hi)
  rw [IntegralMixedPhysicalFieldEqualityList.query_packet] at HI
  have HB:=HI.2.2.2.1
  have HB' : IntegralMixedPhysicalFieldEqualityList.label false (WordList.get table i)<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) cL ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get table i)<
      IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) cR:=by
    simpa only [IntegralMixedPhysicalFieldEquality.Labels,IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample,IntegralMixedPhysicalFieldEquality.label,
      IntegralMixedPhysicalFieldEquality.labelWord,IntegralMixedPhysicalFieldEquality.packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HB
  exact (IntegralMixedPhysicalFieldEquality.language_packet_iff hn ht ha (radius_binary hR0)
    cL wL cR wR HL HR _ _ HB'.1 HB'.2).mp HI

theorem fieldMatch_sound (mean : Bool) (u : List Bool)
    (H : fieldMatch hn ht ha hR0 mean u∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)) :
    ∃hL : SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapAtomic.context (atomic u))
      (IntegralMixedRoadmapAtomic.word (atomic u)),
    ∃hR : SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapProperRow.context hn ht ha hR0 mean (key u)) (ownWord mean u),
    ∀i<IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (key u),
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context (atomic u)) (IntegralMixedRoadmapAtomic.word (atomic u)) hL i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapProperRow.context hn ht ha hR0 mean (key u)) (ownWord mean u) hR i :=by
  obtain ⟨hL,hR,HS⟩:=scan_sound hn ht ha hR0 _ _ _ _ _ H
  refine ⟨hL,hR,fun i hi=>?_⟩
  have HI : i<IntegralMixedRoadmapBadProbePacket.creating (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (atomic u))
      (IntegralMixedRoadmapProper.badPacket (atomic u)):=hi
  have HE:=IntegralMixedRoadmapBadProbePacket.matchTable_lookup
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (atomic u)) (IntegralMixedRoadmapProper.badPacket (atomic u)) i HI
  have HK:=HS i (by rw [IntegralMixedRoadmapBadProbePacket.matchTable_count];exact HI)
  rw [HE] at HK
  simpa only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HK

end LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
