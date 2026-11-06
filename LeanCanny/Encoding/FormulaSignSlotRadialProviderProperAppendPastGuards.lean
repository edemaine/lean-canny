/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastCut
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutSemantics
/-! # Actual historical critical and cut guards on the coherent proper-child word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderAtomic (dimension depth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem proper_cut_root (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (q r : List Bool) (b : ℕ) (hr : pairFst q=r) :
    IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt a d (pairFst q) b).command ↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt a d r b).command := by
  subst r
  rfl
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "stage" => IntegralFramedTraceCutScan.stagePacket
local notation "Cut" => FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
local notation "Guards" => FormulaSignSlotRadialProviderAtomic.Cuts.Guards
local notation "root" => FormulaSignSlotRadialProviderAtomic.root
local notation "word" => FormulaSignSlotRadialProviderAtomic.word

private theorem proper_before_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.Cuts.holds q ↔
    ∀j<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)-1,
      Cut (stage q j)→Guards (stage q j) := Iff.rfl

private theorem proper_cut_shape (q : List Bool) : Cut q ↔ IntegralFramedTraceCutScan.StageCut P D q := Iff.rfl

private theorem proper_probe_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.BeforeProbe q ↔
    FormulaSignSlotRadialProviderAtomic.FullValid q ∧
      FormulaSignSlotRadialProviderAtomic.Cuts.holds (LeanCanny.pair (root q) (word q)) := Iff.rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.root FormulaSignSlotRadialProviderAtomic.word preparedRoot start parentCommands
  IntegralMixedFramedRootPullback.instructionAt IntegralFramedCreatingCut.IsCut
  FormulaSignSlotRadialProviderAtomic.Cuts.StageCut FormulaSignSlotRadialProviderAtomic.Cuts.Guards
  FormulaSignSlotRadialProviderAtomic.Cuts.holds FormulaSignSlotRadialProviderAtomic.BeforeProbe
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalBankTerm.env
  FormulaSignSlotRadialProviderRecordPrefix.ownCutReceipt
  FormulaSignSlotRadialProviderRecordPrefix.observation IntegralMixedPrefixSnapshot.familyCutReceipt

private theorem proper_stage_iff (r w : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    Cut (stage (LeanCanny.pair r w) b) ↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D r b).command := by
  have HJ : b<IntegralFramedTraceCutMetadata.length P D (pairFst (LeanCanny.pair r w))+1 := by
    change b<((D).rules (pairFst (LeanCanny.pair r w))).length+1
    rw [pairFst_pair,full_rules_length]
    omega
  rw [proper_cut_shape]
  exact (IntegralFramedTraceCutOrigin.stageCut_iff P D (LeanCanny.pair r w) b HJ).trans
    (proper_cut_root P D _ r b (pairFst_pair _ _))


variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}

theorem SampledLevel.past_cut_guards (S : SampledLevel old hv hd left right R side pMID pChild)
    (j : ℕ) (hj : j<start old)
    (hb : N (root old)+j<FormulaSignSlotRadialProviderRecordPlan.fullCount (root old)-1)
    (hc : Cut (stage (LeanCanny.pair (preparedRoot old R.leftSpec R.rightSpec side) S.receipt.word) (N (root old)+j))) :
    Guards (stage (LeanCanny.pair (preparedRoot old R.leftSpec R.rightSpec side) S.receipt.word) (N (root old)+j)) := by
  let r := preparedRoot old R.leftSpec R.rightSpec side
  let l := root old
  have HP := prepared_provider old R.leftSpec R.rightSpec side
  have HC := prepared_count old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)
  have HN : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq r l HP
  have HJL : j<IntegralMixedCausalRecordPlanBits.count l := hj.trans_le (start_fit old hv)
  have HJR : j<IntegralMixedCausalRecordPlanBits.count r := HJL.trans_eq HC.symm
  have HBL : N l+j<FormulaSignSlotRadialProviderRecordPlan.fullCount l-1 := hb
  have HH := FormulaSignSlotRadialProviderRecordPrefix.header_eq r l HP HC j
    (Nat.succ_le_of_lt HJR) (fun i hi=>prepared_record old hv R.leftSpec R.rightSpec side i (hi.trans_le (Nat.succ_le_of_lt hj)))
  have HNew : Cut (stage (LeanCanny.pair r S.receipt.word) (N r+j)) := by simpa only [HN] using hc
  have HFull : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  have HI := (proper_stage_iff r S.receipt.word _ HFull).mp HNew
  have HCtx : (IntegralMixedFramedRootPullback.instructionAt P D r (N r+j)).command.context=
      (IntegralMixedFramedRootPullback.instructionAt P D l (N l+j)).command.context := by
    simpa only [FormulaSignSlotRadialProviderRecordPrefix.header_actual,
      IntegralMixedCommandHeaderBits.command_context] using congrArg IntegralMixedCommandHeaderBits.Header.context HH
  have HOld : Cut (stage (LeanCanny.pair l (word old)) (N l+j)) := by
    apply (proper_stage_iff l (word old) _ (by omega)).mpr
    exact (IntegralFramedCreatingCut.isCut_iff_context _).mpr
      (((IntegralFramedCreatingCut.isCut_iff_context _).mp HI).trans_eq HCtx)
  have HBefore : FormulaSignSlotRadialProviderAtomic.Cuts.holds (LeanCanny.pair l (word old)) :=
    ((proper_probe_shape old).mp (FormulaSignSlotRadialProviderAtomic.valid_beforeProbe old hv)).2
  have HG := (proper_before_shape _).mp HBefore _ (by simpa only [pairFst_pair] using hb) HOld
  have HV : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input
      (FormulaSignSlotRadialProviderRecordPrefix.context l) (word old) := FormulaSignSlotRadialProviderAtomic.full_valid old hv
  have HO : Cut (FormulaSignSlotRadialProviderCutReadback.stage l (word old) (N l+j)) := by
    simpa only [FormulaSignSlotRadialProviderCutReadback.stage] using HOld
  have HE := FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt l (word old) HV j HJL HO
  have HR := HE.mp HG
  have HNewReceipt := (past_cut_receipt old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R) S.receipt.word S.receipt.valid (S.receipt.old_raw_native S.old_raw) j hj).mpr HR
  have HGuard := (FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt r S.receipt.word S.receipt.valid j HJR HNew).mpr HNewReceipt
  simpa only [FormulaSignSlotRadialProviderCutReadback.stage,HN] using HGuard

theorem SampledLevel.past_critical (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb : b<FormulaSignSlotRadialProviderAtomic.initial old+start old)
    (ha : FormulaSignSlotRadialProviderAtomic.Active
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side)) b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue FormulaSignSlotRadialProviderRecordPlan.bank
      FormulaSignSlotRadialProviderRecordPlan.tables FormulaSignSlotRadialProviderAtomic.bank_represents
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side))
      S.receipt.word b=InfinitesimalSign.encode 0 :=
  FormulaSignSlotRadialProviderProperAppend.past_critical old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)
    S.receipt.word S.receipt.valid (S.receipt.old_raw_native S.old_raw) b hb ha

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
