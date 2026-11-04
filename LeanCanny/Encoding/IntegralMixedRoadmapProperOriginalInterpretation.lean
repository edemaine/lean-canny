/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowCoordinateTransport
public import LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
/-! # The original accepted word interprets every reserved coordinate parent -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

private def Interprets (A :IntegralMixedPrefixSnapshot.Data) (values :ℕ→ℝ):Prop:=
  ∃φ :A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    ∀i,φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=values (A.birth-1-i.val)

private theorem interprets_transport (A B :IntegralMixedPrefixSnapshot.Data) (he :A=B)
    (values :ℕ→ℝ) (H :Interprets A values):Interprets B values:=by
  subst B
  exact H

private theorem field_root_congr (a b w :List Bool) (he :a=b)
    (ha' :SquareSampleCompleteVertices.Valid SAMP (IntegralMixedMarkedPrefixFieldReadback.context a) w)
    (hb' :SquareSampleCompleteVertices.Valid SAMP (IntegralMixedMarkedPrefixFieldReadback.context b) w) (i :ℕ):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedMarkedPrefixFieldReadback.context a) w ha' i=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedMarkedPrefixFieldReadback.context b) w hb' i:=by
  subst b
  rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.payload
  IntegralMixedMarkedReservedBadSet.snapshot IntegralMixedRoadmapBadProbeParent.snapshot
  IntegralMixedMarkedPrefixSnapshot.snapshot IntegralMixedPhysicalFieldEquality.point
  IntegralMixedRoadmapLocalFrame.field parentKey

private theorem original_snapshot_interprets (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    Interprets (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q))
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv):=by
  obtain ⟨codes,last,Hraw⟩:=IntegralMixedRoadmapLocalFrame.bad_raw_domain hn ht ha hR0 q hv
  let r:=IntegralMixedMarkedPrefixRun.reservedRoot (IntegralMixedRoadmapAtomic.candidate q) codes last []
  have HR :IntegralMixedRoadmapAtomic.root q=r:=by
    have HE:=IntegralMixedRoadmapBadProbeCanonical.root_eq (IntegralMixedRoadmapProper.badPacket q) codes last Hraw
    exact (IntegralMixedRoadmapProper.badPacket_root q).symm.trans (by
      simpa only [r,IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapProper.badPacket,
        IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair] using HE)
  have HW :SquareSampleCompleteVertices.Valid SAMP (IntegralMixedMarkedPrefixFieldReadback.context r)
      (IntegralMixedRoadmapAtomic.word q):=by
    have H:=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv
    simpa only [IntegralMixedRoadmapAtomic.context,HR,IntegralMixedMarkedPrefixFieldReadback.context] using H
  have HWR :SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context r) (IntegralMixedRoadmapAtomic.word q):=by
    rw [IntegralMixedMarkedReservedPoint.input_eq]
    exact HW
  obtain ⟨φ,Hφ⟩:=IntegralMixedMarkedReservedBadSet.exists_interpretation hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate q) codes last [] (IntegralMixedRoadmapAtomic.word q) HWR
  have HV:=IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate q) codes last [] (IntegralMixedRoadmapAtomic.word q) HWR
  have HB : (IntegralMixedMarkedReservedBadSet.snapshot hn ht ha hR0
      (IntegralMixedRoadmapAtomic.candidate q) codes last []).birth=
      IntegralMixedMarkedPrefixFieldReadback.parent n r:=by
    rw [IntegralMixedMarkedReservedBadSet.birth]
    unfold IntegralMixedMarkedPrefixFieldReadback.parent
    dsimp only [r]
    rw [IntegralMixedMarkedPrefixRun.reserved_count]
    omega
  have HC :0<IntegralMixedCausalRecordPlanBits.count r:=by
    dsimp only [r]
    rw [IntegralMixedMarkedPrefixRun.reserved_count]
    omega
  have HI :Interprets (IntegralMixedMarkedReservedBadSet.snapshot hn ht ha hR0
      (IntegralMixedRoadmapAtomic.candidate q) codes last [])
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv):=by
    refine ⟨φ,fun i=>?_⟩
    have HP:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0 r
      (IntegralMixedRoadmapAtomic.word q) HW HC i.val (i.isLt.trans_eq HB)
    have HF:=field_root_congr hn ht ha hR0 r (IntegralMixedRoadmapAtomic.root q)
      (IntegralMixedRoadmapAtomic.word q) HR.symm HW (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
      (IntegralMixedMarkedPrefixFieldReadback.parent n r-1-i.val)
    have HQ :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedMarkedPrefixFieldReadback.context r) (IntegralMixedRoadmapAtomic.word q) HW
        (IntegralMixedMarkedPrefixFieldReadback.parent n r-1-i.val)=
        IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
          (IntegralMixedMarkedPrefixFieldReadback.parent n r-1-i.val):=by
      unfold IntegralMixedRoadmapLocalFrame.field
      exact HF
    exact (Hφ i).trans ((congrFun HV i.val).trans (HP.trans (HQ.trans
      (congrArg (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv)
        (congrArg (fun b :ℕ=>b-1-i.val) HB.symm)))))
  have HE :IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)=
      IntegralMixedMarkedReservedBadSet.snapshot hn ht ha hR0
        (IntegralMixedRoadmapAtomic.candidate q) codes last []:=by
    unfold IntegralMixedRoadmapBadProbeParent.snapshot IntegralMixedMarkedReservedBadSet.snapshot
    simp only [HR,r,IntegralMixedMarkedPrefixRun.reserved_count,Nat.add_sub_cancel]
  exact interprets_transport _ _ HE.symm _ HI

/-- No native row witness or independently sampled coordinate word is needed.
The original full word supplies an honest hom with every original quotient. -/
theorem exists_original_interpretation (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (j :ℕ):
    ∃φ :((G).state (parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ (((G).state (parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).bank.numerator i)/
        (((G).state (parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))).bank.denominator i:ℝ)=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
        ((G).birth (parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j)))-1-i.val):=by
  have HE:=parent_coordinate_snapshot_eq hn ht ha hR0 q
    (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q)) (BinaryNatCode.encode j) hv
  have HO:=IntegralMixedRoadmapLocalFrame.old_snapshot_original hn ht ha hR0 q hv
  have HS :IntegralMixedPrefixSnapshot.ofState
      ((G).state (parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j))))=
      IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q):=
    HE.symm.trans HO
  exact interprets_transport _ _ HS.symm _ (original_snapshot_interprets hn ht ha hR0 q hv)

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
