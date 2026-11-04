/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadEndpoint
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSemantics
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSnapshot
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotRawBad
/-! # The original no-bad guard on the actual ordinary row prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedRoadmapProperRow.parentKey IntegralMixedRoadmapProperRow.dimension
 IntegralMixedRoadmapProperRow.initial IntegralMixedRoadmapProperRow.creating
 IntegralMixedMarkedPrefixSnapshot.snapshot IntegralMixedRoadmapBadProbeParent.snapshot
 IntegralMixedRoadmapProperRow.code IntegralMixedRoadmapProper.badPacket
 IntegralMixedRoadmapBadProbePacket.root IntegralMixedRoadmapAtomic.root
 IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen IntegralMixedRoadmapProper.labels
 IntegralMixedRoadmapAtomic.payload IntegralMixedMarkedPrefixRun.reservedRoot field IntegralMixedPhysicalFieldEquality.point
 IntegralMixedMarkedPrefixFieldReadback.parentPoint

private theorem raw_bad_iff {a S B m : ℕ} {P : SpatialSource a} {ι : Type}
    (x : State P S B m ι) (hm : m≤S) (hx : Canonical x)
    (labels : List Bool) (birth g j : ℕ) (hb : m=birth)
    (hg : g=WordListRecords.count labels+1)
    (H : IntegralMixedChronologicalCutCode.Good a birth labels g j)
    (r : Rule a)
    (hr : r=(IntegralMixedChronologicalCutCode.rawData a birth labels g j H).rule
      (commonDenominator x) (commonDenominator_ne_zero x))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : ℕ→ℝ)
    (hφ : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i.val)
    (c : IntegralMixedRelativeCuts.Choices x hm r φ) (u : ℝ) :
    u∈(IntegralMixedPrefixSnapshot.ofState x).bad labels values ↔
      u∈IntegralMixedSelectedCriticalCuts.bad x hm r φ c :=by
  subst birth
  subst g
  subst r
  exact (IntegralMixedPrefixSnapshot.ofState_mem_bad_iff x hm hx labels j H φ values hφ u).trans
    (IntegralMixedSelectedBadMembership.mem_bad_iff x hm _ φ c u).symm

theorem bad_raw_domain (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    ∃codes last,IntegralMixedRoadmapBadProbePacket.raw (IntegralMixedRoadmapProper.badPacket q)=
      WordList.encode (codes++[last]) :=by
  have HC:=IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv
  refine ⟨IntegralMixedRoadmapChain.meaningfulCodes (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.payload q)++List.replicate
        (IntegralMixedRoadmapChain.paddingCount (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.payload q))
        (IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)),
    IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q),?_⟩
  simpa only [IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.raw,pairFst_pair,pairSnd_pair,
    IntegralMixedRoadmapChain.compiled,IntegralMixedRoadmapChain.compiledCodes] using HC.2.2.2.2.2.1

theorem old_snapshot_original (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q))=
      IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  rw [IntegralMixedRoadmapProperRow.parent_snapshot hn ht ha hR0 false (rowKey q) HC]
  obtain ⟨codes,last,HR⟩:=bad_raw_domain hn ht ha hR0 q hv
  have HP:=IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq _ codes last HR
  have HE:=IntegralMixedRoadmapBadProbeCanonical.root_eq _ codes last HR
  have HE' : IntegralMixedRoadmapAtomic.root q=
      IntegralMixedMarkedPrefixRun.reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last []:=
    (IntegralMixedRoadmapProper.badPacket_root q).symm.trans (by
      simpa only [IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapProper.badPacket,
        IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair] using HE)
  have HRight : IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)=
      IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0
        (IntegralMixedMarkedPrefixRun.reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last [])
        codes.length (by rw [IntegralMixedMarkedPrefixRun.reserved_count];omega):=by
    unfold IntegralMixedRoadmapBadProbeParent.snapshot
    simp only [HE',IntegralMixedMarkedPrefixRun.reserved_count,Nat.add_sub_cancel]
  rw [HRight]
  unfold IntegralMixedRoadmapProperRow.parentSnapshot
  simp only [IntegralMixedRoadmapProperRow.row_root_reserved,IntegralMixedRoadmapProperRow.oldPacket,
    IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,HP]
  exact IntegralMixedMarkedPrefixSnapshot.reserved_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate q) codes
    (IntegralMixedRoadmapProperRow.code hn ht ha hR0 false (rowKey q)) last [] []

private theorem old_birth_row (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    (G).birth (oldKey hn ht ha hR0 q)=IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false (rowKey q) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth (BK).parameters (BK).plan (BK).data _).trans
    ((IntegralMixedRoadmapProperRow.parentKey_prefix hn ht ha hR0 false (rowKey q) HC).trans
      (IntegralMixedRoadmapProperRow.parentBirth_eq hn ht ha hR0 false (rowKey q) HC).symm)

attribute [local semireducible] IntegralMixedFramedHistoryFamilyBits.family

theorem old_bad_iff (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val))
    (c : IntegralMixedRelativeCuts.Choices ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ) (a : ℝ) :
    a∈(IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q))).bad
      (IntegralMixedRoadmapProper.labels q)
      (fun i=>field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i)) ↔
    a∈IntegralMixedSelectedCriticalCuts.bad ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ c :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  have HG:=(IntegralMixedRoadmapProperRow.parent_good hn ht ha hR0 false (rowKey q) HC HR).1
  have Hrule:=IntegralMixedRoadmapProperRow.rule_at_parent hn ht ha hR0 false (rowKey q) HC HR
  simp only [IntegralMixedRoadmapProperRow.parentData,Bool.false_eq_true,ite_false] at Hrule
  have Hoffset : IntegralMixedRoadmapProperRow.offset (rowKey q)=
      WordListRecords.count (IntegralMixedRoadmapProperRow.labels (rowKey q))+1:=by
    simp only [IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.labels,
      IntegralMixedRoadmapProper.labels_count]
  have Hready:=raw_bad_iff ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _)
    (IntegralMixedRoadmapProperRow.parent_canonical hn ht ha hR0 false (rowKey q) HC)
    (IntegralMixedRoadmapProperRow.labels (rowKey q))
    (IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false (rowKey q))
    (IntegralMixedRoadmapProperRow.offset (rowKey q)) (IntegralMixedRoadmapProperRow.coordinate (rowKey q))
    (old_birth_row hn ht ha hR0 q hv) Hoffset HG ((G).rule (oldKey hn ht ha hR0 q)) Hrule
  simpa only [IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair]
    using Hready φ (fun i=>field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i)) Hφ c a

private theorem parent_point_congr (a b u v : List Bool) (hab : a=b) (huv : u=v)
    (ha' : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context a) u)
    (hb' : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context b) v) :
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 a u ha'=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 b v hb':=by
  subst b
  subst v
  rfl

theorem no_bad_of_base (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val))
    (c : IntegralMixedRelativeCuts.Choices ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ) :
    ∀a,a∈Set.Ioo (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
      (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))→
      a∉IntegralMixedSelectedCriticalCuts.bad ((G).state (oldKey hn ht ha hR0 q))
        ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ c :=by
  obtain ⟨codes,last,Hraw⟩:=bad_raw_domain hn ht ha hR0 q hv
  have HFit : ∀side,IntegralMixedRoadmapBadProbePacket.producer side (IntegralMixedRoadmapProper.badPacket q)<
      IntegralMixedMarkedPrefixFieldReadback.parent n
        (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q)):=by
    intro side
    rw [bad_packet_producer,IntegralMixedRoadmapProper.badPacket_root]
    exact bad_producer_lt_parent hn ht ha hR0 q HR side
  have HOrder : IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
      (bad_full_valid hn ht ha hR0 q hv) false<
    IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
      (bad_full_valid hn ht ha hR0 q hv) true:=by
    rw [bad_endpoint hn ht ha hR0 q hv HR false,bad_endpoint hn ht ha hR0 q hv HR true]
    exact order_of_base hn ht ha hR0 q hv HB
  have HNo:=(IntegralMixedRoadmapBadProbeSemantics.noBadProbe_iff hn ht ha hR0
    (IntegralMixedRoadmapProper.badPacket q) codes last Hraw (bad_full_valid hn ht ha hR0 q hv) HFit HOrder).mp HB.2.2.2.1
  have HS:=old_snapshot_original hn ht ha hR0 q hv
  have HBirth : (G).birth (oldKey hn ht ha hR0 q)=
      IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q):=by
    have HE:=congrArg IntegralMixedPrefixSnapshot.Data.birth HS
    exact HE.trans (IntegralMixedRoadmapBadProbeParent.birth hn ht ha hR0 _
      (bad_record_positive hn ht ha hR0 q hv))
  have HValues : ∀i,i<(IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey hn ht ha hR0 q))).birth→
      field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i)=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) i:=by
    intro i hi
    have HI : i<IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root q):=hi.trans_eq HBirth
    rw [HBirth]
    exact (bad_parent_values hn ht ha hR0 q hv i HI).symm
  have HE:=IntegralMixedPrefixSnapshot.Data.bad_transport _ _ HS (IntegralMixedRoadmapProper.labels q) _ _ HValues
  intro a haInterval Hbad
  have HOld:=(old_bad_iff hn ht ha hR0 q hv HR φ Hφ c a).mpr Hbad
  rw [HE] at HOld
  have HA : a∈Set.Ioo
      (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
        (bad_full_valid hn ht ha hR0 q hv) false)
      (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
        (bad_full_valid hn ht ha hR0 q hv) true):=by
    simpa only [bad_endpoint hn ht ha hR0 q hv HR] using haInterval
  apply HNo a HA
  have HLabels : IntegralMixedRoadmapBadProbePacket.labels (IntegralMixedRoadmapProper.badPacket q)=
      IntegralMixedRoadmapProper.labels q:=by
    simp only [IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapProper.badPacket,
      IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  have HPP:=parent_point_congr hn ht ha hR0 _ _ _ _ (IntegralMixedRoadmapProper.badPacket_root q)
    (bad_packet_word q) (bad_full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
  change a∈(IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0
    (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q))).bad
    (IntegralMixedRoadmapBadProbePacket.labels (IntegralMixedRoadmapProper.badPacket q))
    (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
      (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q))
      (IntegralMixedRoadmapBadProbePacket.word (IntegralMixedRoadmapProper.badPacket q))
      (bad_full_valid hn ht ha hR0 q hv))
  rw [HPP,IntegralMixedRoadmapProper.badPacket_root,HLabels]
  exact HOld

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
