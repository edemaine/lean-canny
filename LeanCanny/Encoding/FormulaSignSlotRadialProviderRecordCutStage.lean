/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixMetadata
public import LeanCanny.Encoding.IntegralMixedMarkedCutReceipt
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotFamily
/-! # Provider cut stages use their actual chronological prefix algebra -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count

noncomputable def cutParent (r : List Bool) (b : ℕ) :=
  IntegralFramedPhysicalTraceCutSource.parent B (context r) (List.replicate b true)
noncomputable def cutSaved (r : List Bool) (b : ℕ) := IntegralMixedVirtualTaskBits.saved P (cutParent r b)

theorem cutParent_eq (r : List Bool) (b : ℕ) : cutParent r b=
    IntegralFramedTraceCutTask.task P (pair r (pair (List.replicate b true) [])) := by
  simp only [cutParent,IntegralFramedPhysicalTraceCutSource.parent,context,pairFst_pair]
  rfl

theorem cut_stage_bound (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) : b≤birthCap P r := by
  change b≤FormulaSignSlotRadialProviderRecordPlan.fullCount r+2+1
  omega

theorem cutSaved_eq (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    cutSaved r b=keyAt r b (BinaryNatCode.encode 2) := by
  unfold cutSaved
  rw [cutParent_eq]
  have HB : IntegralFramedTraceCutTask.stage (pair r (pair (List.replicate b true) []))≤
      birthCap P (pairFst (pair r (pair (List.replicate b true) []))) := by
    simpa only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair,List.length_replicate] using cut_stage_bound r b hb
  simpa only [pairFst_pair,IntegralFramedTraceCutTask.stage_packet,List.length_replicate] using
    IntegralFramedTraceCutTask.task_saved P (pair r (pair (List.replicate b true) [])) HB

theorem cutParent_birth (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) : birth P (cutParent r b)=b := by
  rw [cutParent_eq]
  have HB : IntegralFramedTraceCutTask.stage (pair r (pair (List.replicate b true) []))≤
      birthCap P (pairFst (pair r (pair (List.replicate b true) []))) := by
    simpa only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair,List.length_replicate] using cut_stage_bound r b hb
  simpa only [IntegralFramedTraceCutTask.stage_packet,List.length_replicate] using
    IntegralFramedTraceCutTask.task_birth P (pair r (pair (List.replicate b true) [])) HB

theorem cutSaved_birth (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) : (G).birth (cutSaved r b)=b :=
  ((geometry P D H).birth (cutParent r b)).trans (cutParent_birth r b hb)

theorem instruction_initial (key : List Bool) : (instruction P D key).source=(D).initialSource (pairFst key) := by
  rw [IntegralMixedFramedNormalizationBits.planned_instruction]
  exact FormulaSignSlotRadialProviderRecordPlan.instruction_source key

theorem snapshot_family_keyAt (r : List Bool) (j : ℕ)
    (hj : j≤IntegralMixedCausalRecordPlanBits.count r) (aux : List Bool) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (keyAt r (N r+j) aux))=snapshot r j hj := by
  exact (IntegralMixedPrefixSnapshot.family_eq_original P D H _ (instruction_initial _)).trans
    (IntegralMixedPrefixSnapshot.original_keyAt P D r aux (N r+j) (bound r j hj))

theorem cut_snapshot (r : List Bool) (j : ℕ) (hj : j<IntegralMixedCausalRecordPlanBits.count r) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (cutSaved r (N r+j)))=snapshot r j hj.le := by
  have HB : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  exact (congrArg (fun k=>IntegralMixedPrefixSnapshot.ofState ((G).state k)) (cutSaved_eq r _ HB)).trans
    (snapshot_family_keyAt r j hj.le (BinaryNatCode.encode 2))

theorem cut_active (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    IntegralMixedFramedFullCutProbeBits.Active P (cutParent r b) := by
  constructor
  · change birth P (cutParent r b)<(P).cap (RankedHistoryTask.root (cutParent r b))
    rw [cutParent_birth r b hb]
    have HR : RankedHistoryTask.root (cutParent r b)=r := by
      rw [cutParent_eq,IntegralFramedTraceCutTask.task_root,pairFst_pair]
    rw [HR]
    change b<FormulaSignSlotRadialProviderRecordPlan.fullCount r+2
    omega
  · have HE := IntegralFramedTraceCutTask.task_context P (pair r (pair (List.replicate b true) []))
    rw [←cutParent_eq r b] at HE
    change 2≤get P .slot15 (cutParent r b) ∧ get P .slot15 (cutParent r b)≤4
    rw [HE]
    decide

noncomputable def ownCutReceipt (r w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w)
    (j : ℕ) (hj : j<IntegralMixedCausalRecordPlanBits.count r) : Prop :=
  IntegralMixedPrefixSnapshot.familyCutReceipt P D H (cutSaved r (N r+j))
    ((observation r j hj.le).point (natural r w hw))
    (FormulaSignSlotRadialProviderAtomic.bankField (context r) w hw (N r+j))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
