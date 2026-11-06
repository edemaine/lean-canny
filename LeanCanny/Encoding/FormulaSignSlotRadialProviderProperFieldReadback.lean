/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
/-! # Accepted row witnesses preserve every actual older retained value -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

private theorem scan_sound (cL wL cR wR table : List Bool)
    (H : FormulaSignSlotRadialProviderFieldEqualityList.packet cL wL cR wR table∈
      FormulaSignSlotRadialProviderFieldEqualityList.language) :
    ∃hL : SquareSampleCompleteVertices.Valid S cL wL,∃hR : SquareSampleCompleteVertices.Valid S cR wR,
      ∀i<WordListRecords.count table,
        FormulaSignSlotRadialProviderFieldEquality.point cL wL hL
          (FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get table i))=
        FormulaSignSlotRadialProviderFieldEquality.point cR wR hR
          (FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get table i)) :=by
  have HL : SquareSampleCompleteVertices.Valid S cL wL:=by
    simpa only [FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.word,
      FormulaSignSlotRadialProviderFieldEquality.sample,FormulaSignSlotRadialProviderFieldEqualityList.packet,
      Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using H.1
  have HR : SquareSampleCompleteVertices.Valid S cR wR:=by
    simpa only [FormulaSignSlotRadialProviderFieldEquality.context,FormulaSignSlotRadialProviderFieldEquality.word,
      FormulaSignSlotRadialProviderFieldEquality.sample,FormulaSignSlotRadialProviderFieldEqualityList.packet,
      ite_true,pairFst_pair,pairSnd_pair] using H.2.1
  refine ⟨HL,HR,fun i hi=>?_⟩
  have HI:=H.2.2 i (by simpa only [FormulaSignSlotRadialProviderFieldEqualityList.count,
    FormulaSignSlotRadialProviderFieldEqualityList.table,FormulaSignSlotRadialProviderFieldEqualityList.packet,pairSnd_pair] using hi)
  rw [FormulaSignSlotRadialProviderFieldEqualityList.query_packet] at HI
  have HB:=HI.2.2.2.1
  have HB' : FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get table i)<
      FormulaSignSlotRadialProviderFieldEquality.count cL ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get table i)<
      FormulaSignSlotRadialProviderFieldEquality.count cR:=by
    simpa only [FormulaSignSlotRadialProviderFieldEquality.Labels,FormulaSignSlotRadialProviderFieldEquality.context,
      FormulaSignSlotRadialProviderFieldEquality.sample,FormulaSignSlotRadialProviderFieldEquality.label,
      FormulaSignSlotRadialProviderFieldEquality.labelWord,FormulaSignSlotRadialProviderFieldEquality.packet,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HB
  exact (FormulaSignSlotRadialProviderFieldEquality.language_packet_iff
    cL wL cR wR HL HR _ _ HB'.1 HB'.2).mp HI

theorem fieldMatch_sound (mean : Bool) (u : List Bool)
    (H : fieldMatch mean u∈FormulaSignSlotRadialProviderFieldEqualityList.language) :
    ∃hL : SquareSampleCompleteVertices.Valid S (FormulaSignSlotRadialProviderAtomic.context (atomic u))
      (FormulaSignSlotRadialProviderAtomic.word (atomic u)),
    ∃hR : SquareSampleCompleteVertices.Valid S (FormulaSignSlotRadialProviderProperRow.context mean (key u)) (ownWord mean u),
    ∀i<FormulaSignSlotRadialProviderProperRow.creating (key u),
      FormulaSignSlotRadialProviderFieldEquality.point
        (FormulaSignSlotRadialProviderAtomic.context (atomic u)) (FormulaSignSlotRadialProviderAtomic.word (atomic u)) hL i=
      FormulaSignSlotRadialProviderFieldEquality.point
        (FormulaSignSlotRadialProviderProperRow.context mean (key u)) (ownWord mean u) hR i :=by
  obtain ⟨hL,hR,HS⟩:=scan_sound _ _ _ _ _ H
  refine ⟨hL,hR,fun i hi=>?_⟩
  have HI : i<IntegralMixedRoadmapBadProbePacket.creating (FormulaSignSlotRadialProviderAtomic.initial (atomic u))
      (IntegralMixedRoadmapProper.badPacket (atomic u)):=hi
  have HE:=IntegralMixedRoadmapBadProbePacket.matchTable_lookup
    (FormulaSignSlotRadialProviderAtomic.initial (atomic u)) (IntegralMixedRoadmapProper.badPacket (atomic u)) i HI
  have HK:=HS i (by rw [IntegralMixedRoadmapBadProbePacket.matchTable_count];exact HI)
  rw [HE] at HK
  simpa only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HK

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
