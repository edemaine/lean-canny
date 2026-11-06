/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbePrefix
/-! # Bad probes compare every actual older chronological field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeFields
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapBadProbePacket (root preparedRoot count creating matchTable)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "S" => FormulaSignSlotRadialProviderAtomic.input
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context

def packet (d initial : ℕ) (z w : List Bool) := FormulaSignSlotRadialProviderFieldEqualityList.packet
  (C (root (pairFst z))) (IntegralMixedRoadmapBadProbePacket.word (pairFst z)) (C (preparedRoot d z)) w
  (matchTable initial (pairFst z))

theorem initial_eq (base : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.bank.parameters.ambient (root base)+5=N (root base) := by
  change FormulaSignSlotRadialExternalPrelude.number (FormulaSignSlotRadialProviderRecordPlan.providerContext (root base))+3+5=
    FormulaSignSlotRadialExternalPrelude.number (FormulaSignSlotRadialProviderRecordPlan.providerContext (root base))+8
  omega

theorem left_count (base : List Bool) : FormulaSignSlotRadialProviderFieldEquality.count (C (root base))=N (root base)+count base := by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [FormulaSignSlotRadialProviderRecordPrefix.context,pairFst_pair,FormulaSignSlotRadialProviderRecordPlan.fullCount,
    FormulaSignSlotRadialProviderBadProbePrefix.root_count]

theorem right_count (d : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    FormulaSignSlotRadialProviderFieldEquality.count (C (preparedRoot d z))=N (root (pairFst z))+count (pairFst z) := by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [FormulaSignSlotRadialProviderRecordPrefix.context,pairFst_pair,FormulaSignSlotRadialProviderRecordPlan.fullCount]
  rw [FormulaSignSlotRadialProviderBadProbePrefix.prepared_initial,
    IntegralMixedRoadmapBadProbePacket.prepared_count d z hc]

theorem packet_iff (d initial : ℕ) (z w : List Bool) (hc : 0<count (pairFst z))
    (hi : initial=N (root (pairFst z)))
    (hL : SquareSampleCompleteVertices.Valid S (C (root (pairFst z))) (IntegralMixedRoadmapBadProbePacket.word (pairFst z)))
    (hR : SquareSampleCompleteVertices.Valid S (C (preparedRoot d z)) w) :
    packet d initial z w∈FormulaSignSlotRadialProviderFieldEqualityList.language ↔
      ∀i<creating initial (pairFst z),
        FormulaSignSlotRadialProviderAtomic.bankField (C (root (pairFst z)))
          (IntegralMixedRoadmapBadProbePacket.word (pairFst z)) hL i=
        FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot d z)) w hR i := by
  have HL : FormulaSignSlotRadialProviderFieldEquality.count (C (root (pairFst z)))=creating initial (pairFst z)+1 := by
    rw [left_count,hi]
    unfold creating
    omega
  have HR : FormulaSignSlotRadialProviderFieldEquality.count (C (preparedRoot d z))=creating initial (pairFst z)+1 := by
    rw [right_count d z hc,hi]
    unfold creating
    omega
  have HE (i : ℕ) (h : i<creating initial (pairFst z)) :
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get (matchTable initial (pairFst z)) i)=i ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get (matchTable initial (pairFst z)) i)=i := by
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup initial (pairFst z) i h]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,and_self]
  have HB : ∀i<WordListRecords.count (matchTable initial (pairFst z)),
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get (matchTable initial (pairFst z)) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (C (root (pairFst z))) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get (matchTable initial (pairFst z)) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (C (preparedRoot d z)) := by
    intro i h
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_count] at h
    rw [(HE i h).1,(HE i h).2,HL,HR]
    omega
  rw [packet,FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff _ _ _ _ _ hL hR HB,
    IntegralMixedRoadmapBadProbePacket.matchTable_count]
  constructor <;> intro H i h
  · have H0 := H i h
    rw [(HE i h).1,(HE i h).2,FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ i (by rw [HL];omega),
      FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ i (by rw [HR];omega)] at H0
    exact H0
  · rw [(HE i h).1,(HE i h).2,FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ i (by rw [HL];omega),
      FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ i (by rw [HR];omega)]
    exact H i h

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeFields
