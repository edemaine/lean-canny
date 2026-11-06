/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCutStage
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualitySemantics
/-! # Actual provider interval contexts recover their saved creating prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G" => family P D H

private theorem snapshot_count (a : Parameters) (d : Plan a)
    (h : IntegralMixedFramedHistoryFamilyBits.Data a d) (k : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey a d h k).count=(family a d h).birth k := rfl

theorem cap_eq (r : List Bool) : (P).cap r=FormulaSignSlotRadialProviderRecordPlan.fullCount r+2 := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank family

theorem key_root (q : List Bool) : pairFst ((B).key q)=pairFst q :=
  (congrArg pairFst (FormulaSignSlotRadialProviderAtomic.Cuts.key_context q)).trans
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (pairFst q))

theorem bank_birth (q : List Bool) : (G).birth ((B).key q)=count q := by
  unfold count
  exact (snapshot_count P D H ((B).key q)).symm

theorem count_eq (q : List Bool) : count q=FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q) :=
  (bank_birth q).symm.trans (FormulaSignSlotRadialProviderFieldEquality.count_eq q)

theorem parent_root (q : List Bool) : RankedHistoryTask.root (parent q)=pairFst q := by
  unfold parent
  rw [IntegralFramedTraceCutTask.task_root,pairFst_pair]

attribute [local irreducible] parent
  FormulaSignSlotRadialProviderAtomic.Cuts.StageCut IntegralFramedCreatingCut.ParentCut

theorem stage_bound (q w : List Bool) (hb : Bounds (pair q w)) :
    (birthWord q).length≤birthCap P (pairFst q) := by
  have HJ : (birthWord q).length<count q := by simpa only [pairFst_pair] using hb.2.2.1
  have HC : count q≤(P).cap (pairFst q)+1 := by
    rw [count_eq,cap_eq]
    omega
  exact HJ.le.trans HC

theorem parent_saved (q w : List Bool) (hb : Bounds (pair q w)) :
    IntegralMixedVirtualTaskBits.saved P (parent q)=keyAt (pairFst q) (birthWord q).length (BinaryNatCode.encode 2) := by
  have HB : IntegralFramedTraceCutTask.stage (pair (pairFst q) (pair (birthWord q) []))≤
      birthCap P (pairFst (pair (pairFst q) (pair (birthWord q) []))) := by
    simpa only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair] using stage_bound q w hb
  simpa only [parent,pairFst_pair,IntegralFramedTraceCutTask.stage_packet] using
    IntegralFramedTraceCutTask.task_saved P (pair (pairFst q) (pair (birthWord q) [])) HB

theorem parent_birth (q w : List Bool) (hb : Bounds (pair q w)) :
    (G).birth (IntegralMixedVirtualTaskBits.saved P (parent q))=(birthWord q).length := by
  rw [parent_saved q w hb]
  exact (family_birth P D H _).trans (keyAt_prefix P _ _ _ (stage_bound q w hb))

theorem fits (q w : List Bool) (hb : Bounds (pair q w)) :
    (G).birth (IntegralMixedVirtualTaskBits.saved P (parent q))≤(G).birth ((B).key q) := by
  rw [parent_birth q w hb]
  rw [bank_birth]
  exact (by simpa only [pairFst_pair] using hb.2.2.1 : (birthWord q).length<count q).le

theorem parent_cut (q w : List Bool) (hb : Bounds (pair q w)) :
    IntegralFramedCreatingCut.ParentCut P D (parent q) := by
  have HC : FormulaSignSlotRadialProviderAtomic.Cuts.StageCut (guardPacket (pair q w)) := by
    unfold Bounds at hb
    exact hb.2.2.2
  unfold FormulaSignSlotRadialProviderAtomic.Cuts.StageCut IntegralFramedTraceCutScan.StageCut at HC
  change IntegralFramedCreatingCut.ParentCut P D
    (IntegralFramedTraceCutGuards.parent P (guardPacket (pair q w))) at HC
  have HP : IntegralFramedTraceCutGuards.parent P (guardPacket (pair q w))=parent q := by
    simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
      IntegralFramedTraceCutGuards.root,guardPacket,parent,pairFst_pair,pairSnd_pair]
  exact HP ▸ HC

theorem active (q w : List Bool) (hb : Bounds (pair q w)) :
    IntegralMixedFramedFullCutProbeBits.Active P (parent q) := by
  have HJ : (birthWord q).length<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q) := by
    rw [←count_eq]
    simpa only [pairFst_pair] using hb.2.2.1
  constructor
  · change birth P (parent q)<(P).cap (RankedHistoryTask.root (parent q))
    rw [parent_root,←(geometry P D H).birth (parent q),parent_birth q w hb]
    rw [cap_eq]
    omega
  · have HE : get P .slot15 (parent q)=2 := by
      simpa only [parent] using
        IntegralFramedTraceCutTask.task_context P (pair (pairFst q) (pair (birthWord q) []))
    change 2≤get P .slot15 (parent q) ∧ get P .slot15 (parent q)≤4
    rw [HE]
    decide

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
