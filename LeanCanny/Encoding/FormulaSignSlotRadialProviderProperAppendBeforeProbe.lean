/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastGuards
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendMetadata
/-! # The same constructed proper word satisfies the entire native before-probe scan -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderAtomic (dimension depth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem before_cut_root (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
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

private theorem before_before_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.Cuts.holds q ↔
    ∀j<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)-1,
      Cut (stage q j)→Guards (stage q j) := Iff.rfl

private theorem before_cut_shape (q : List Bool) : Cut q ↔ IntegralFramedTraceCutScan.StageCut P D q := Iff.rfl

private theorem before_probe_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.BeforeProbe q ↔
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
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.ownBirth

private theorem before_stage_iff (r w : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    Cut (stage (LeanCanny.pair r w) b) ↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D r b).command := by
  have HJ : b<IntegralFramedTraceCutMetadata.length P D (pairFst (LeanCanny.pair r w))+1 := by
    change b<((D).rules (pairFst (LeanCanny.pair r w))).length+1
    rw [pairFst_pair,full_rules_length]
    omega
  rw [before_cut_shape]
  exact (IntegralFramedTraceCutOrigin.stageCut_iff P D (LeanCanny.pair r w) b HJ).trans
    (before_cut_root P D _ r b (pairFst_pair _ _))


variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}

theorem SampledLevel.cuts_hold (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.Cuts.holds
      (LeanCanny.pair (preparedRoot old R.leftSpec R.rightSpec side) S.receipt.word) := by
  apply (before_before_shape _).mpr
  intro b hb hc
  simp only [pairFst_pair] at hb
  let r := preparedRoot old R.leftSpec R.rightSpec side
  have HFull : FormulaSignSlotRadialProviderRecordPlan.fullCount r=
      FormulaSignSlotRadialProviderRecordPlan.fullCount (root old) := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    rw [FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider old R.leftSpec R.rightSpec side),
      prepared_count old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)]
  have HB : b<fullBirth old hv hd left right R side := by
    exact hb.trans_le (Nat.sub_le _ _)
  by_cases hmid : midpointBirth old hv hd left right R≤b
  · exact False.elim ((no_cut_after_midpoint old hv hd left right R side b hmid HB)
      ((before_stage_iff r S.receipt.word b HB).mp hc))
  · by_cases hnew : beginBirth old≤b
    · exact S.endpoint_cut_guard old hv hd left right R side b hnew (by omega) hc
    · by_cases hinit : b<N (root old)
      · have HI := (before_stage_iff r S.receipt.word b HB).mp hc
        have HH := FormulaSignSlotRadialProviderFirstSeed.integer_header r b
          (hinit.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _
            (prepared_provider old R.leftSpec R.rightSpec side)).symm)
        have HE := (IntegralFramedCreatingCut.isCut_iff_context _).mp HI
        have HCtx : (IntegralMixedFramedRootPullback.instructionAt P D r b).command.context=0 := by
          simpa only [FormulaSignSlotRadialProviderFirstSeed.stageHeader,
            IntegralMixedCommandHeaderBits.command_context,IntegralMixedCommandHeaderBits.zero] using
            congrArg IntegralMixedCommandHeaderBits.Header.context HH
        omega
      · have HL : N (root old)≤b := by omega
        obtain ⟨j,HJ⟩ := Nat.exists_eq_add_of_le HL
        subst b
        have HBegin : beginBirth old=N (root old)+start old := by
          simpa only [FormulaSignSlotRadialProviderAtomic.initial] using begin_eq_start old
        have HCount : FormulaSignSlotRadialProviderRecordPlan.fullCount
            (preparedRoot old R.leftSpec R.rightSpec side)=
            FormulaSignSlotRadialProviderRecordPlan.fullCount (root old) := HFull
        have HOldBound : N (root old)+j<FormulaSignSlotRadialProviderRecordPlan.fullCount (root old)-1 :=
          hb.trans_eq (congrArg (fun n : ℕ=>n-1) HCount)
        exact S.past_cut_guards j (by omega) HOldBound hc

theorem SampledLevel.before_probe (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.BeforeProbe
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) := by
  apply (before_probe_shape _).mpr
  refine ⟨S.receipt.full_valid,?_⟩
  simpa only [FormulaSignSlotRadialProviderAtomic.fullQuery,root_packet,word_packet] using S.cuts_hold

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
