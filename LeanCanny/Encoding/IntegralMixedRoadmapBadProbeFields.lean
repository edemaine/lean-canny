/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
/-! # The reserved-probe field scan compares every actual old quotient

The two complete words stay in their own sampler contexts. The final
chronological producer is excluded; no point-map equality is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeFields
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapBadProbePacket (root preparedRoot count creating matchTable)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leftContext (q : List Bool):=pair (root q) []
def rightContext (d : ℕ) (z : List Bool):=pair (preparedRoot d z) []
def packet (d initial : ℕ) (z w : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (leftContext (pairFst z)) (IntegralMixedRoadmapBadProbePacket.word (pairFst z))
  (rightContext d z) w (matchTable initial (pairFst z))

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

theorem initial_eq (q : List Bool) :
    (B).parameters.ambient (root q)+5=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8 :=by
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+3+5=_
  omega

theorem left_count (q : List Bool) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha hR (leftContext q)=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8+count q :=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [leftContext,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,
    IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,root,pairSnd_pair,count]

theorem prepared_number (d : ℕ) (z : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.number n (preparedRoot d z)=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (root (pairFst z)) :=by
  change n (pairFst (pairFst (preparedRoot d z)))=n (pairFst (pairFst (root (pairFst z))))
  simp only [preparedRoot,root,pairFst_pair]

theorem right_count (d : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha hR (rightContext d z)=
      IntegralMixedAuxiliaryMarkedIntegerSource.number n (root (pairFst z))+8+count (pairFst z) :=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [rightContext,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  rw [IntegralMixedRoadmapBadProbePacket.prepared_count d z hc,prepared_number d z]

theorem counts (d initial : ℕ) (z : List Bool) (hc : 0<count (pairFst z))
    (hi : initial=(B).parameters.ambient (root (pairFst z))+5) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha hR (leftContext (pairFst z))=
        creating initial (pairFst z)+1 ∧
    IntegralMixedPhysicalFieldEquality.count hn ht ha hR (rightContext d z)=
        creating initial (pairFst z)+1 :=by
  rw [left_count hn ht ha hR,right_count hn ht ha hR d z hc]
  rw [hi,initial_eq hn ht ha hR]
  simp only [creating]
  omega

theorem packet_iff (d initial : ℕ) (z w : List Bool) (hc : 0<count (pairFst z))
    (hi : initial=(B).parameters.ambient (root (pairFst z))+5)
    (hL : SquareSampleCompleteVertices.Valid S (leftContext (pairFst z))
      (IntegralMixedRoadmapBadProbePacket.word (pairFst z)))
    (hR' : SquareSampleCompleteVertices.Valid S (rightContext d z) w) :
    packet d initial z w∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR ↔
      ∀i<creating initial (pairFst z),
        IntegralMixedPhysicalFieldEquality.point hn ht ha hR (leftContext (pairFst z))
          (IntegralMixedRoadmapBadProbePacket.word (pairFst z)) hL i=
        IntegralMixedPhysicalFieldEquality.point hn ht ha hR (rightContext d z) w hR' i :=by
  have HL:= (counts hn ht ha hR d initial z hc hi).1
  have HR:= (counts hn ht ha hR d initial z hc hi).2
  have HE (i : ℕ) (h : i<creating initial (pairFst z)) :
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (matchTable initial (pairFst z)) i)=i ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (matchTable initial (pairFst z)) i)=i :=by
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup initial (pairFst z) i h]
    simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,and_self]
  have HB : ∀i<WordListRecords.count (matchTable initial (pairFst z)),
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (matchTable initial (pairFst z)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha hR (leftContext (pairFst z)) ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (matchTable initial (pairFst z)) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha hR (rightContext d z) :=by
    intro i h
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_count] at h
    rw [(HE i h).1,(HE i h).2,HL,HR]
    omega
  rw [packet,IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha hR _ _ _ _ _ hL hR' HB,
    IntegralMixedRoadmapBadProbePacket.matchTable_count]
  constructor <;> intro H i h
  · simpa only [(HE i h).1,(HE i h).2] using H i h
  · simpa only [(HE i h).1,(HE i h).2] using H i h
end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeFields
