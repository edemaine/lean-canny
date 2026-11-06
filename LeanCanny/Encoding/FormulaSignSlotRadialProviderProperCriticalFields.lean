/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalSound
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalParentFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList
/-! # The critical-parent word agrees with the original node on every old field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
local notation "Q"=>query
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>FormulaSignSlotRadialProviderCriticalPrefixes.key false
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


theorem fields_sound (q wF wP : List Bool)
    (H : fields (pair (pair q wF) wP)∈
      FormulaSignSlotRadialProviderFieldEqualityList.language) :
    ∃hL : SquareSampleCompleteVertices.Valid S (FormulaSignSlotRadialProviderAtomic.context q)
      (FormulaSignSlotRadialProviderAtomic.word q),
    ∃hR : SquareSampleCompleteVertices.Valid S (context q) wF,
    ∀i<IntegralMixedRoadmapBadProbePacket.creating
        (FormulaSignSlotRadialProviderAtomic.initial q) (IntegralMixedRoadmapProper.badPacket q),
      FormulaSignSlotRadialProviderFieldEquality.point
        (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q) hL i=
      FormulaSignSlotRadialProviderFieldEquality.point
        (context q) wF hR i :=by
  have HH : FormulaSignSlotRadialProviderFieldEqualityList.packet (FormulaSignSlotRadialProviderAtomic.context q)
      (FormulaSignSlotRadialProviderAtomic.word q) (context q) wF
      (IntegralMixedRoadmapBadProbePacket.matchTable (FormulaSignSlotRadialProviderAtomic.initial q)
        (IntegralMixedRoadmapProper.badPacket q))∈FormulaSignSlotRadialProviderFieldEqualityList.language:=by
    simpa only [fields,atomic,fullWord,pairFst_pair,pairSnd_pair] using H
  obtain ⟨hL,hR,HS⟩:=scan_sound _ _ _ _ _ HH
  refine ⟨hL,hR,fun i hi=>?_⟩
  have HK:=HS i (by rw [IntegralMixedRoadmapBadProbePacket.matchTable_count];exact hi)
  rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup _ _ i hi] at HK
  simpa only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HK

theorem query_context (q w : List Bool) : FormulaSignSlotRadialProviderCriticalContext.context (Q (pair q w))=
    context q :=by
  rw [FormulaSignSlotRadialProviderCriticalContext.context,root_word]
  rfl

private theorem field_context_eq (c d w : List Bool) (he : c=d)
    (hc : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w) (i : ℕ) :
    FormulaSignSlotRadialProviderFieldEquality.point c w hc i=
      FormulaSignSlotRadialProviderFieldEquality.point d w hd i :=by
  subst d
  rfl

attribute [local irreducible] FormulaSignSlotRadialProviderFieldEquality.point
  FormulaSignSlotRadialProviderCriticalInterval.parentValues SquareSampleCompleteVertices.Valid
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus


theorem witness_parent_fields (q wF wP : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (H : Witness (pair (pair q wF) wP))
    (hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP)))) :
    ∀i : Fin ((G).birth (K (Q (pair q wP)))),
      FormulaSignSlotRadialProviderCriticalInterval.parentValues (Q (pair q wP)) hp i=
        FormulaSignSlotRadialProviderFieldEquality.point
          (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
          (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
          (FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))-1-i.val) :=by
  obtain ⟨hL,hR,HM⟩:=fields_sound q wF wP H.2.2.2.1
  have HF : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input true) (Q (pair q wP)) wF:=by
    simpa only [critical,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using H.2.2.1
  have HC : SquareSampleCompleteVertices.Valid S (FormulaSignSlotRadialProviderCriticalContext.context (Q (pair q wP))) wF:=by
    rw [query_context]
    exact hR
  have HG : FormulaSignSlotRadialProviderCriticalBankEquality.agrees
      (pair (Q (pair q wP)) wF):=by
    simpa only [joint,critical,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using H.2.2.2.2.1
  intro i
  have HE:=FormulaSignSlotRadialProviderCriticalContext.parentValues_field
    (Q (pair q wP)) wF hp HF HC HG i
  have HB : FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))=
      IntegralMixedRoadmapBadProbePacket.creating (FormulaSignSlotRadialProviderAtomic.initial q)
        (IntegralMixedRoadmapProper.badPacket q):=by
    rw [query_birth q wP (count_positive q hv)]
    rfl
  have HI : FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))-1-i.val<
      IntegralMixedRoadmapBadProbePacket.creating (FormulaSignSlotRadialProviderAtomic.initial q)
        (IntegralMixedRoadmapProper.badPacket q):=by
    have Hpos:=FormulaSignSlotRadialProviderCriticalPrefixes.birth_pos false (Q (pair q wP))
    rw [←HB]
    omega
  have HM':=HM _ HI
  exact HE.trans ((field_context_eq _ _ wF (query_context q wP)
    HC hR _).trans HM'.symm)

theorem query_endpoint (side : Bool) (q w : List Bool) :
    Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q w))
      else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q w)))=IntegralMixedRoadmapProper.producer side q :=by
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,query,
    IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    IntegralMixedPhysicalCriticalQuery.rightWord,IntegralMixedPhysicalCriticalQuery.leftWord,
    IntegralMixedPhysicalCriticalQuery.prepare,IntegralMixedPhysicalCriticalQuery.withEndpoints,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] query FormulaSignSlotRadialProviderCriticalPrefixes.birth
  FormulaSignSlotRadialProviderCriticalInterval.endpointValue
  IntegralMixedPhysicalCriticalQuery.leftWord IntegralMixedPhysicalCriticalQuery.rightWord

theorem witness_endpoint_field (side : Bool) (q wF wP : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (H : Witness (pair (pair q wF) wP))
    (hp : SquareSampleCompleteVertices.Valid
      (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP)))) :
    FormulaSignSlotRadialProviderCriticalInterval.endpointValue (Q (pair q wP)) hp
      (Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q wP))
        else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q wP))))=
    FormulaSignSlotRadialProviderFieldEquality.point
      (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
      (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (IntegralMixedRoadmapProper.producer side q) :=by
  have HG : FormulaSignSlotRadialProviderCriticalInterval.Guard (Q (pair q wP)):=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.1
  have hj : IntegralMixedRoadmapProper.producer side q<FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP)):=by
    have HE : Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q wP))
        else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q wP)))<
          FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP)):=by
      cases side
      · exact HG.2.1
      · exact HG.2.2
    exact (congrArg (fun v : ℕ=>v<FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP)))
      (query_endpoint side q wP)).mp HE
  let i : Fin ((G).birth (K (Q (pair q wP)))):=
    ⟨FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))-1-IntegralMixedRoadmapProper.producer side q,
      by rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false];omega⟩
  have HE:=witness_parent_fields q wF wP hv H hp i
  have HX : FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))-1-i.val=
      IntegralMixedRoadmapProper.producer side q:=by dsimp only [i];omega
  rw [HX] at HE
  rw [query_endpoint]
  unfold FormulaSignSlotRadialProviderCriticalInterval.endpointValue
  exact (FormulaSignSlotRadialProviderCriticalContext.parentValues_point
    (Q (pair q wP)) hp i).symm.trans HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
