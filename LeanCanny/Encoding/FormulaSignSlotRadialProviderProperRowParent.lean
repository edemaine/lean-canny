/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCutStage
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixSemantics

/-! # The reserved row query names its literal, unclipped creating prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem canonical_of_snapshot {n S W m : ℕ} {Q : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State Q S W m ι) (d : IntegralMixedPrefixSnapshot.Data)
    (he : IntegralMixedPrefixSnapshot.ofState x=d) (hc : IntegralMixedHistory.Canonical d.state) :
    IntegralMixedHistory.Canonical x :=by
  exact (congrArg (fun a : IntegralMixedPrefixSnapshot.Data=>IntegralMixedHistory.Canonical a.state) he).mpr hc

local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
attribute [local irreducible] dimension initial creating

noncomputable def parentKey (mean : Bool) (z : List Bool):=
  IntegralMixedVirtualTaskBits.saved P (parent mean z)

theorem root_provider (mean : Bool) (z : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext (root mean z)=
      FormulaSignSlotRadialProviderAtomic.provider (atomic z) :=pairFst_pair _ _

theorem root_initial (mean : Bool) (z : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.count (root mean z)=initial z :=by
  unfold initial FormulaSignSlotRadialProviderAtomic.initial
  exact FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _
    ((root_provider mean z).trans (FormulaSignSlotRadialProviderAtomic.root_provider _).symm)

theorem root_dimension (mean : Bool) (z : List Bool) : (P).ambient (root mean z)=dimension z :=by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root mean z))=_
  rw [root_provider]
  unfold dimension
  exact (FormulaSignSlotRadialProviderAtomic.dimension_provider (atomic z)).symm

theorem root_count (mean : Bool) (z : List Bool) (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedCausalRecordPlanBits.count (root mean z)=IntegralMixedRoadmapBadProbePacket.count (oldPacket z):=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    root,raw,pairFst_pair,pairSnd_pair,WordListRecords.count_encode,List.length_append,List.length_singleton,
    IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
  omega

theorem raw_last (mean : Bool) (z : List Bool) : WordList.get (raw mean z)
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)=code mean z :=by
  have HL : IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1=
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length:=by
    simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
  rw [HL,raw,WordList.get_encode]
  simp

theorem raw_older (mean : Bool) (z : List Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1) :
    WordList.get (raw mean z) i=WordList.get (IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)) i :=by
  have HL : i<(IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length:=by
    simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range]
    exact hi
  rw [raw,WordList.get_encode,List.getElem?_append_left HL]
  simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some]

theorem creating_bound (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    creating z≤birthCap P (root mean z) :=by
  change creating z≤FormulaSignSlotRadialProviderRecordPlan.fullCount (root mean z)+2+1
  rw [FormulaSignSlotRadialProviderRecordPlan.fullCount,root_initial,root_count mean z hc]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating
  omega

theorem parent_root (mean : Bool) (z : List Bool) :
    RankedHistoryTask.root (parent mean z)=root mean z :=by
  rw [parent,IntegralMixedRoutineContextQuery.query_root]
  exact RankedHistoryTask.root_pack _ _ _ _

theorem parent_birth (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    birth P (parent mean z)=creating z :=by
  apply IntegralMixedRoutineContextQuery.query_birth
  rw [base,RankedHistoryTask.root_pack]
  exact creating_bound mean z hc

theorem parentKey_root (mean : Bool) (z : List Bool) :
    pairFst (parentKey mean z)=root mean z :=by
  simp only [parentKey,IntegralMixedVirtualTaskBits.saved,pairFst_pair,parent_root]

theorem parentKey_prefix (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    prefixLength P (parentKey mean z)=creating z :=by
  change prefixLength P (IntegralMixedFramedHistoryFamilyBits.keyAt _ _ _)=_
  rw [IntegralMixedFramedHistoryFamilyBits.keyAt_prefix]
  · exact parent_birth mean z hc
  · rw [parent_root,parent_birth mean z hc]
    exact creating_bound mean z hc

theorem parentKey_records (mean : Bool) (z : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (pairFst (parentKey mean z))=
      WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++[code mean z]) :=by
  rw [parentKey_root]
  simp only [IntegralMixedCausalRecordPlanBits.records,root,pairFst_pair,pairSnd_pair,raw]

theorem parentKey_eq (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    parentKey mean z=IntegralMixedFramedHistoryFamilyBits.keyAt (root mean z) (creating z)
      (BinaryNatCode.encode (get P Field.slot15 (parent mean z))) :=by
  unfold parentKey IntegralMixedVirtualTaskBits.saved
  rw [parent_root,parent_birth mean z hc]

attribute [local irreducible] parentKey FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
noncomputable def parentSnapshot (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot (root mean z)
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)
    (by rw [root_count mean z hc];omega)

theorem parent_snapshot (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey mean z))=
      parentSnapshot mean z hc :=by
  have HS:=FormulaSignSlotRadialProviderRecordPrefix.snapshot_family_keyAt (root mean z)
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)
    (by rw [root_count mean z hc];omega)
    (BinaryNatCode.encode (get P Field.slot15 (parent mean z)))
  have HB : FormulaSignSlotRadialProviderRecordPlan.count (root mean z)+
      (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)=creating z:=by
    rw [root_initial]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating
    omega
  rw [HB,←parentKey_eq mean z hc] at HS
  simpa only [parentSnapshot,FormulaSignSlotRadialProviderRecordPlan.bank] using HS

theorem parent_state_snapshot_eq (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey false z))=
      IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey true z)) :=by
  rw [parent_snapshot false z hc,parent_snapshot true z hc]
  have HP := (root_provider false z).trans (root_provider true z).symm
  have HC : IntegralMixedCausalRecordPlanBits.count (root false z)=
      IntegralMixedCausalRecordPlanBits.count (root true z):=by
    rw [root_count false z hc,root_count true z hc]
  have HCodes : ∀i,i<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1→
      IntegralMixedCausalRecordPlanBits.code (root false z) i=
        IntegralMixedCausalRecordPlanBits.code (root true z) i:=by
    intro i hi
    simp only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
      root,pairSnd_pair,pairFst_pair]
    exact (raw_older false z i hi).trans (raw_older true z i hi).symm
  exact FormulaSignSlotRadialProviderRecordPrefix.snapshot_eq _ _ HP HC
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)
    (by rw [root_count false z hc];omega) HCodes

theorem parent_canonical (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedHistory.Canonical ((family P D H).state (parentKey mean z)) :=by
  have HE:=parent_snapshot mean z hc
  have HC:=FormulaSignSlotRadialProviderRecordPrefix.snapshot_canonical (root mean z)
    (IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1)
    (by rw [root_count mean z hc];omega)
  exact canonical_of_snapshot _ _ HE HC

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
