/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPacket
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPastCut
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutSemantics
/-! # Historical native cut guards on the fresh retained-child word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem retained_cut_root (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
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

private theorem retained_before_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.Cuts.holds q ↔
    ∀j<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)-1,
      Cut (stage q j)→Guards (stage q j) := Iff.rfl

private theorem retained_cut_shape (q : List Bool) : Cut q ↔ IntegralFramedTraceCutScan.StageCut P D q := Iff.rfl

private theorem retained_probe_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.BeforeProbe q ↔
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

private theorem retained_stage_iff (r w : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    Cut (stage (LeanCanny.pair r w) b) ↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D r b).command := by
  have HJ : b<IntegralFramedTraceCutMetadata.length P D (pairFst (LeanCanny.pair r w))+1 := by
    change b<((D).rules (pairFst (LeanCanny.pair r w))).length+1
    rw [pairFst_pair,full_rules_length]
    omega
  rw [retained_cut_shape]
  exact (IntegralFramedTraceCutOrigin.stageCut_iff P D (LeanCanny.pair r w) b HJ).trans
    (retained_cut_root P D _ r b (pairFst_pair _ _))


variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (FormulaSignSlotRadialProviderAtomic.initial old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.past_cut_guards (W : WordReceipt old hv hd e he p)
    (j : ℕ) (hj : j<start old)
    (hb : N (root old)+j<FormulaSignSlotRadialProviderRecordPlan.fullCount (root old)-1)
    (hc : Cut (stage (LeanCanny.pair (preparedRoot old e) W.word) (N (root old)+j))) :
    Guards (stage (LeanCanny.pair (preparedRoot old e) W.word) (N (root old)+j)) := by
  let r := preparedRoot old e
  let l := root old
  have HP := prepared_provider old e
  have HC := prepared_count old hv hd e he
  have HN : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq r l HP
  have HJL : j<IntegralMixedCausalRecordPlanBits.count l := hj.trans_le (start_fit old hv)
  have HJR : j<IntegralMixedCausalRecordPlanBits.count r := HJL.trans_eq HC.symm
  have HBL : N l+j<FormulaSignSlotRadialProviderRecordPlan.fullCount l-1 := hb
  have HH := FormulaSignSlotRadialProviderRecordPrefix.header_eq r l HP HC j
    (Nat.succ_le_of_lt HJR) (fun i hi=>prepared_record old hv e i (hi.trans_le (Nat.succ_le_of_lt hj)))
  have HNew : Cut (stage (LeanCanny.pair r W.word) (N r+j)) := by simpa only [HN] using hc
  have HFull : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  have HI := (retained_stage_iff r W.word _ HFull).mp HNew
  have HCtx : (IntegralMixedFramedRootPullback.instructionAt P D r (N r+j)).command.context=
      (IntegralMixedFramedRootPullback.instructionAt P D l (N l+j)).command.context := by
    simpa only [FormulaSignSlotRadialProviderRecordPrefix.header_actual,
      IntegralMixedCommandHeaderBits.command_context] using congrArg IntegralMixedCommandHeaderBits.Header.context HH
  have HOld : Cut (stage (LeanCanny.pair l (word old)) (N l+j)) := by
    apply (retained_stage_iff l (word old) _ (by omega)).mpr
    exact (IntegralFramedCreatingCut.isCut_iff_context _).mpr
      (((IntegralFramedCreatingCut.isCut_iff_context _).mp HI).trans_eq HCtx)
  have HBefore : FormulaSignSlotRadialProviderAtomic.Cuts.holds (LeanCanny.pair l (word old)) :=
    ((retained_probe_shape old).mp (FormulaSignSlotRadialProviderAtomic.valid_beforeProbe old hv)).2
  have HG := (retained_before_shape _).mp HBefore _ (by simpa only [pairFst_pair] using hb) HOld
  have HV : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input
      (FormulaSignSlotRadialProviderRecordPrefix.context l) (word old) := FormulaSignSlotRadialProviderAtomic.full_valid old hv
  have HO : Cut (FormulaSignSlotRadialProviderCutReadback.stage l (word old) (N l+j)) := by
    simpa only [FormulaSignSlotRadialProviderCutReadback.stage] using HOld
  have HE := FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt l (word old) HV j HJL HO
  have HR := HE.mp HG
  have HNewReceipt := (past_cut_receipt old hv hd e he W.word W.valid W.old_raw_native j hj).mpr HR
  have HGuard := (FormulaSignSlotRadialProviderCutSemantics.guards_iff_ownReceipt r W.word W.valid j HJR HNew).mpr HNewReceipt
  simpa only [FormulaSignSlotRadialProviderCutReadback.stage,HN] using HGuard

theorem WordReceipt.cuts_hold (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.Cuts.holds (LeanCanny.pair (preparedRoot old e) W.word) := by
  apply (retained_before_shape _).mpr
  intro b hb hc
  have HC := prepared_count old hv hd e he
  have HFull : FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e)=
      FormulaSignSlotRadialProviderRecordPlan.fullCount (root old) := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    rw [FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old e),HC]
  have HB : b<FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e) := by
    simp only [pairFst_pair] at hb
    omega
  by_cases hnew : N (root old)+start old≤b
  · have HNo := no_cut_after_begin old hv hd e he b hnew HB
    exact False.elim (HNo ((retained_stage_iff _ _ _ HB).mp hc))
  · by_cases hinit : b<N (root old)
    · have HI := (retained_stage_iff _ _ _ HB).mp hc
      have HH := FormulaSignSlotRadialProviderFirstSeed.integer_header (preparedRoot old e) b
        (hinit.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old e)).symm)
      have HE := (IntegralFramedCreatingCut.isCut_iff_context _).mp HI
      have HCtx : (IntegralMixedFramedRootPullback.instructionAt P D (preparedRoot old e) b).command.context=0 := by
        simpa only [FormulaSignSlotRadialProviderFirstSeed.stageHeader,
          IntegralMixedCommandHeaderBits.command_context,IntegralMixedCommandHeaderBits.zero] using
          congrArg IntegralMixedCommandHeaderBits.Header.context HH
      omega
    · have HL : N (root old)≤b := by omega
      obtain ⟨j,HJ⟩ := Nat.exists_eq_add_of_le HL
      subst b
      exact W.past_cut_guards j (by omega) (by simpa only [pairFst_pair,HFull] using hb) hc

theorem WordReceipt.before_probe (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.BeforeProbe (packet (dimension old) old e W.word) := by
  apply (retained_probe_shape _).mpr
  refine ⟨W.full_valid,?_⟩
  simpa only [FormulaSignSlotRadialProviderAtomic.fullQuery,root_packet,word_packet] using W.cuts_hold

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
