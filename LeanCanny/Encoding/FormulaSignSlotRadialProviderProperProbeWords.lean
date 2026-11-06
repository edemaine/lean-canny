/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbePrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReservedCutRealization
/-! # Actual fresh ordinary and mean provider probe words -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem dependent_exists_map {α : Type*} (pp : α→Prop) (qq rr : ∀a,pp a→Prop)
    (h : ∃a,∃ha : pp a,qq a ha) (hh : ∀a ha,qq a ha → rr a ha) :
    ∃a,∃ha : pp a,rr a ha :=by
  obtain ⟨a,ha,HQ⟩:=h
  exact ⟨a,ha,hh a ha HQ⟩

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

theorem probe_cut_table (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    IntegralMixedCausalRecordPlanBits.records (pairFst (parentKey mean z))=
      WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++
        [(parentData mean z (parent_good mean z hc hg)).code
          (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0]) :=by
  rw [parentData_code]
  exact parentKey_records mean z

theorem probe_prefix_length (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    prefixLength P (parentKey mean z)=FormulaSignSlotRadialProviderRecordPlan.count (pairFst (parentKey mean z))+
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length :=by
  have HE:=(parentKey_prefix mean z hc).trans (parentBirth_eq mean z hc).symm
  simpa only [parentBirth] using HE

theorem probe_run_realizes (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (parentKey mean z)))
        ((D).rules (pairFst (parentKey mean z))) (by have HR:=(D).room (pairFst (parentKey mean z));omega))
      (IntegralFramedPaddedCutVertex.values (probeValues z hv)) :=by
  have HC:=row_count_positive z hv
  exact FormulaSignSlotRadialProviderReservedCutRealization.run_realizes
    (parentKey mean z) (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z))
    (parentData mean z (parent_good mean z HC hg)) (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0
    (Nat.zero_le _) (probe_cut_table mean z HC hg) (probe_prefix_length mean z HC)
    (probeValues z hv) (probe_parent_realizes mean z hv)

theorem probe_rules_length (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ((D).rules (pairFst (parentKey mean z))).length=
      FormulaSignSlotRadialProviderRecordPlan.count (pairFst (parentKey mean z))+
        (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length+1 :=
  FormulaSignSlotRadialProviderReservedCutRealization.rules_length (parentKey mean z)
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)) _ (probe_cut_table mean z hc hg)

theorem probe_full_count (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    (G).birth ((B).key (context mean z))=creating z+1 :=by
  have HC:=row_count_positive z hv
  calc
    (G).birth ((B).key (context mean z))=
        FormulaSignSlotRadialProviderRecordPlan.fullCount (root mean z) :=by
      change FormulaSignSlotRadialProviderFieldEquality.count (context mean z)=_
      simpa only [context,pairFst_pair] using FormulaSignSlotRadialProviderFieldEquality.count_eq (context mean z)
    _=creating z+1 :=by
      rw [FormulaSignSlotRadialProviderRecordPlan.fullCount,root_initial,root_count mean z HC]
      unfold creating IntegralMixedRoadmapBadProbePacket.creating
      omega

theorem probe_completed_length (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ((D).rules (pairFst (parentKey mean z))).length=creating z+1 :=by
  have HC:=row_count_positive z hv
  have HE:=(probe_prefix_length mean z HC).symm.trans (parentKey_prefix mean z HC)
  exact (probe_rules_length mean z HC hg).trans (congrArg (fun m : ℕ=>m+1) HE)

theorem exists_probe_word (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context mean z) w,
      w.length=SquareSampleCompleteVertices.width FormulaSignSlotRadialProviderAtomic.input (context mean z) ∧
      ∀i : Fin ((G).birth ((B).key (context mean z))),
        IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context mean z) w hw i=
          IntegralFramedPaddedCutVertex.values (probeValues z hv) i.val :=by
  have HR : pairFst ((B).key (context mean z))=pairFst (parentKey mean z):=by
    have HE:=FormulaSignSlotRadialProviderFieldEquality.key_root (context mean z)
    have HE' : pairFst ((B).key (context mean z))=root mean z:=by
      simpa only [context,pairFst_pair] using HE
    exact HE'.trans (parentKey_root mean z).symm
  have HL : prefixLength P ((B).key (context mean z))=((D).rules (pairFst (parentKey mean z))).length:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm.trans
      ((probe_full_count mean z hv).trans (probe_completed_length mean z hv hg).symm)
  exact IntegralMixedReservedCutActualVertex.vertex_from_full_run P D H L F C hs (B).key (B).positive
    (context mean z) (pairFst (parentKey mean z)) HR HL
    (IntegralFramedPaddedCutVertex.values (probeValues z hv)) (probe_run_realizes mean z hv hg)

private theorem fields_of_point_values (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context mean z) w)
    (HP : ∀i : Fin ((G).birth ((B).key (context mean z))),
      IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context mean z) w hw i=
        IntegralFramedPaddedCutVertex.values (probeValues z hv) i.val) :
    ∀p<creating z,FormulaSignSlotRadialProviderFieldEquality.point (context mean z) w hw p=
      originalValue (atomic z) hv p :=by
  intro p hp
  have HB:=probe_full_count mean z hv
  have HI : p<FormulaSignSlotRadialProviderFieldEquality.count (context mean z):=by
    change p<(G).birth ((B).key (context mean z))
    omega
  let j : Fin ((G).birth ((B).key (context mean z))):=
    ⟨(G).birth ((B).key (context mean z))-1-p,by omega⟩
  have HField : FormulaSignSlotRadialProviderFieldEquality.point (context mean z) w hw p=
      IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context mean z) w hw j:=
    (FormulaSignSlotRadialProviderFieldEquality.point_env (context mean z) w hw p HI).trans
      (IntegralFramedPhysicalBankTerm.env_chronological B FormulaSignSlotRadialProviderRecordPlan.tables
        FormulaSignSlotRadialProviderAtomic.bank_represents (context mean z) w hw p HI)
  have HJval : j.val=creating z-p:=by dsimp only [j];omega
  have HJ : j.val≠0:=by rw [HJval];omega
  have HJold : j.val-1<creating z:=by rw [HJval];omega
  have HIndex : creating z-1-(j.val-1)=p:=by rw [HJval];omega
  have HW:=HP j
  simp only [IntegralFramedPaddedCutVertex.values,HJ,ite_false] at HW
  exact HField.trans (HW.trans ((probeValues_field z hv (j.val-1) HJold).trans
    (congrArg (originalValue (atomic z) hv) HIndex)))

theorem exists_probe_fields (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context mean z) w,
      w.length=SquareSampleCompleteVertices.width FormulaSignSlotRadialProviderAtomic.input (context mean z) ∧
      ∀p<creating z,FormulaSignSlotRadialProviderFieldEquality.point (context mean z) w hw p=
        originalValue (atomic z) hv p :=by
  have HH:=exists_probe_word mean z hv hg
  exact dependent_exists_map _ _ _ HH (by
    intro w hw h
    exact ⟨h.1,fields_of_point_values mean z hv w hw h.2⟩)

theorem probe_width_context (mean : Bool) (z : List Bool) :
    SquareSampleCompleteVertices.width
      (IntegralFramedPhysicalSquare.input P D H L F C hs (terminal mean) (positive mean)) z=
    SquareSampleCompleteVertices.width FormulaSignSlotRadialProviderAtomic.input (context mean z) :=by
  rw [sampler_comp mean]
  exact SquareSampleCompleteNaturality.complete_width_comp _ _ _

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
