/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperOrder
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowRuling
/-! # Bad-probe endpoints are the original local endpoint fields

The row grammar bounds both endpoint producers before the reserved final
record. The parent observation reads the same full word and actual bank.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapProperRow.dimension
  IntegralMixedRoadmapProperRow.initial IntegralMixedRoadmapProperRow.creating

theorem bad_packet_word (q : List Bool) :
    IntegralMixedRoadmapBadProbePacket.word (IntegralMixedRoadmapProper.badPacket q)=
      IntegralMixedRoadmapAtomic.word q :=by
  simp only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.word,pairFst_pair,pairSnd_pair]

theorem bad_packet_producer (side : Bool) (q : List Bool) :
    IntegralMixedRoadmapBadProbePacket.producer side (IntegralMixedRoadmapProper.badPacket q)=
      IntegralMixedRoadmapProper.producer side q :=by
  cases side <;> simp only [IntegralMixedRoadmapBadProbePacket.producer,
    IntegralMixedRoadmapBadProbePacket.endpoints,IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair,
    Bool.false_eq_true,ite_false,ite_true,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem bad_packet_count (q : List Bool) :
    IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)=
      IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q) :=by
  simp only [IntegralMixedRoadmapBadProbePacket.count,IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair]

theorem bad_packet_initial (q : List Bool) :
    (B).parameters.ambient (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q))+5=
      IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q :=by
  rw [IntegralMixedRoadmapProper.badPacket_root]
  rw [IntegralMixedRoadmapAtomic.initial,IntegralMixedRoadmapAtomic.dimension]

theorem bad_parent_birth (q : List Bool) :
    IntegralMixedRoadmapBadProbePacket.creating
      ((B).parameters.ambient (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q))+5)
      (IntegralMixedRoadmapProper.badPacket q)=
        IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q) :=by
  have HI:=IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapProper.badPacket q)
  rw [IntegralMixedRoadmapProper.badPacket_root] at HI
  unfold IntegralMixedRoadmapBadProbePacket.creating IntegralMixedMarkedPrefixFieldReadback.parent
  rw [IntegralMixedRoadmapProper.badPacket_root,HI,bad_packet_count]

theorem bad_full_valid (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    SquareSampleCompleteVertices.Valid S
      (IntegralMixedMarkedPrefixFieldReadback.context
        (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q)))
      (IntegralMixedRoadmapBadProbePacket.word (IntegralMixedRoadmapProper.badPacket q)) :=by
  rw [IntegralMixedRoadmapProper.badPacket_root,bad_packet_word]
  exact IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv

theorem bad_producer_lt_parent (q : List Bool)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q)) (side : Bool) :
    IntegralMixedRoadmapProper.producer side q<
      IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q) :=by
  have HB : IntegralMixedRoadmapProper.producer side q<
      IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (rowKey q) :=by
    cases side
    · have HL:=HR.2.2.1
      simpa only [IntegralMixedRoadmapProperRow.oldProducer,IntegralMixedRoadmapProperRow.atomic,
        rowKey,pairFst_pair] using HL
    · have HL:=HR.2.2.2.1
      simpa only [IntegralMixedRoadmapProperRow.oldProducer,IntegralMixedRoadmapProperRow.atomic,
        rowKey,pairFst_pair] using HL
  have HE : IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (rowKey q)=
      IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q) :=by
    rw [IntegralMixedRoadmapProperRow.creating,IntegralMixedRoadmapProperRow.initial,
      IntegralMixedRoadmapProperRow.oldPacket]
    simp only [IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair]
    rw [←bad_packet_initial hn ht ha hR0 q]
    exact bad_parent_birth hn ht ha hR0 q
  exact HB.trans_eq HE

theorem bad_record_positive (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    0<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  simpa only [IntegralMixedRoadmapProperRow.oldPacket,IntegralMixedRoadmapProperRow.atomic,
    rowKey,pairFst_pair,bad_packet_count] using HC

attribute [local irreducible] field IntegralMixedPhysicalFieldEquality.point
  IntegralMixedMarkedPrefixFieldReadback.parentPoint

theorem bad_parent_values (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : ℕ) (hi : i<IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)) :
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) i=
        field hn ht ha hR0 q hv
          (IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)-1-i) :=by
  unfold field
  exact IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
    (bad_record_positive hn ht ha hR0 q hv) i hi



theorem bad_endpoint (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q)) (side : Bool) :
    IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
      (bad_full_valid hn ht ha hR0 q hv) side=
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer side q) :=by
  have HB:=bad_producer_lt_parent hn ht ha hR0 q HR side
  have HP:=bad_parent_values hn ht ha hR0 q hv
    (IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)-1-
      IntegralMixedRoadmapProper.producer side q) (by omega)
  have HE : IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)-1-
      (IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q)-1-
        IntegralMixedRoadmapProper.producer side q)=IntegralMixedRoadmapProper.producer side q:=by omega
  rw [HE] at HP
  unfold IntegralMixedRoadmapBadProbeSound.endpoint
  rw [bad_parent_birth hn ht ha hR0 q]
  simpa only [bad_packet_word,IntegralMixedRoadmapProper.badPacket_root,bad_packet_producer] using HP

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
