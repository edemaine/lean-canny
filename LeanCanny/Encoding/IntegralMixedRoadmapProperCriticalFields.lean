/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalSound
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperFieldReadback
/-! # The critical-parent word agrees with the original node on every old field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "Q"=>query hn ht ha hR0
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>IntegralMixedPhysicalCriticalPrefixes.key n false false
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


theorem fields_sound (q wF wP : List Bool)
    (H : fields hn ht ha hR0 (pair (pair q wF) wP)∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)) :
    ∃hL : SquareSampleCompleteVertices.Valid S (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.word q),
    ∃hR : SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 q) wF,
    ∀i<IntegralMixedRoadmapBadProbePacket.creating
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapProper.badPacket q),
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hL i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (context hn ht ha hR0 q) wF hR i :=by
  have HH : IntegralMixedPhysicalFieldEqualityList.packet (IntegralMixedRoadmapAtomic.context q)
      (IntegralMixedRoadmapAtomic.word q) (context hn ht ha hR0 q) wF
      (IntegralMixedRoadmapBadProbePacket.matchTable (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
        (IntegralMixedRoadmapProper.badPacket q))∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
    simpa only [fields,atomic,fullWord,pairFst_pair,pairSnd_pair] using H
  obtain ⟨hL,hR,HS⟩:=scan_sound hn ht ha hR0 _ _ _ _ _ HH
  refine ⟨hL,hR,fun i hi=>?_⟩
  have HK:=HS i (by rw [IntegralMixedRoadmapBadProbePacket.matchTable_count];exact hi)
  rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup _ _ i hi] at HK
  simpa only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HK

theorem query_context (q w : List Bool) : IntegralMixedPhysicalCriticalContext.context (Q (pair q w))=
    context hn ht ha hR0 q :=by
  rw [IntegralMixedPhysicalCriticalContext.context,root_word]
  rfl

private theorem field_context_eq (c d w : List Bool) (he : c=d)
    (hc : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w) (i : ℕ) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) c w hc i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) d w hd i :=by
  subst d
  rfl

attribute [local irreducible] IntegralMixedPhysicalFieldEquality.point
  IntegralMixedPhysicalCriticalInterval.parentValues SquareSampleCompleteVertices.Valid
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus


theorem witness_parent_fields (q wF wP : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (H : Witness hn ht ha hR0 (pair (pair q wF) wP))
    (hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP)))) :
    ∀i : Fin ((G).birth (K (Q (pair q wP)))),
      IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false (Q (pair q wP)) hp i=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
          (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
          (IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))-1-i.val) :=by
  obtain ⟨hL,hR,HM⟩:=fields_sound hn ht ha hR0 q wF wP H.2.2.2.1
  have HF : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false true) (Q (pair q wP)) wF:=by
    simpa only [critical,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using H.2.2.1
  have HC : SquareSampleCompleteVertices.Valid S (IntegralMixedPhysicalCriticalContext.context (Q (pair q wP))) wF:=by
    rw [query_context]
    exact hR
  have HG : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (radius_binary hR0) false
      (pair (Q (pair q wP)) wF):=by
    simpa only [joint,critical,atomic,parentWord,fullWord,pairFst_pair,pairSnd_pair] using H.2.2.2.2.1
  intro i
  have HE:=IntegralMixedPhysicalCriticalContext.parentValues_field hn ht ha (radius_binary hR0)
    (Q (pair q wP)) wF hp HF HC HG i
  have HB : IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))=
      IntegralMixedRoadmapBadProbePacket.creating (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
        (IntegralMixedRoadmapProper.badPacket q):=by
    rw [query_birth hn ht ha hR0 q wP (count_positive hn ht ha hR0 q hv)]
    rfl
  have HI : IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))-1-i.val<
      IntegralMixedRoadmapBadProbePacket.creating (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
        (IntegralMixedRoadmapProper.badPacket q):=by
    have Hpos:=IntegralMixedPhysicalCriticalPrefixes.birth_pos n false false (Q (pair q wP))
    rw [←HB]
    omega
  have HM':=HM _ HI
  exact HE.trans ((field_context_eq hn ht ha hR0 _ _ wF (query_context hn ht ha hR0 q wP)
    HC hR _).trans HM'.symm)

theorem query_endpoint (side : Bool) (q w : List Bool) :
    Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q w))
      else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q w)))=IntegralMixedRoadmapProper.producer side q :=by
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,query,
    IntegralMixedPhysicalCriticalQuery.packet,IntegralMixedPhysicalCriticalQuery.root,
    IntegralMixedPhysicalCriticalQuery.rightWord,IntegralMixedPhysicalCriticalQuery.leftWord,
    IntegralMixedPhysicalCriticalQuery.prepare,IntegralMixedPhysicalCriticalQuery.withEndpoints,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] query IntegralMixedPhysicalCriticalPrefixes.birth
  IntegralMixedPhysicalCriticalInterval.endpointValue
  IntegralMixedPhysicalCriticalQuery.leftWord IntegralMixedPhysicalCriticalQuery.rightWord

theorem witness_endpoint_field (side : Bool) (q wF wP : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (H : Witness hn ht ha hR0 (pair (pair q wF) wP))
    (hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
      (Q (pair q wP)) (IntegralMixedPhysicalCriticalQuery.parentWord (Q (pair q wP)))) :
    IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha (radius_binary hR0) false (Q (pair q wP)) hp
      (Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q wP))
        else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q wP))))=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapProper.producer side q) :=by
  have HG : IntegralMixedPhysicalCriticalInterval.Guard n false (Q (pair q wP)):=by
    simpa only [critical,atomic,parentWord,pairFst_pair,pairSnd_pair] using H.1
  have hj : IntegralMixedRoadmapProper.producer side q<IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP)):=by
    have HE : Nat.fromBitsLE (if side then IntegralMixedPhysicalCriticalQuery.rightWord (Q (pair q wP))
        else IntegralMixedPhysicalCriticalQuery.leftWord (Q (pair q wP)))<
          IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP)):=by
      cases side
      · exact HG.2.1
      · exact HG.2.2
    exact (congrArg (fun v : ℕ=>v<IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP)))
      (query_endpoint hn ht ha hR0 side q wP)).mp HE
  let i : Fin ((G).birth (K (Q (pair q wP)))):=
    ⟨IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))-1-IntegralMixedRoadmapProper.producer side q,
      by rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha (radius_binary hR0) false false];omega⟩
  have HE:=witness_parent_fields hn ht ha hR0 q wF wP hv H hp i
  have HX : IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))-1-i.val=
      IntegralMixedRoadmapProper.producer side q:=by dsimp only [i];omega
  rw [HX] at HE
  rw [query_endpoint]
  unfold IntegralMixedPhysicalCriticalInterval.endpointValue
  exact (IntegralMixedPhysicalCriticalContext.parentValues_point hn ht ha (radius_binary hR0)
    (Q (pair q wP)) hp i).symm.trans HE

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
