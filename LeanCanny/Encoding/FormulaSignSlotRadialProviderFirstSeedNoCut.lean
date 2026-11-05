/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedWord
public import LeanCanny.Encoding.IntegralFramedTraceCutOrigin
/-! # Source-aware seed histories contain no creating cut -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open IntegralMixedFramedHistoryFamilyBits (Plan)

def CutFreeAt (P : Parameters) (D : Plan P) (r : List Bool) (b : ℕ) : Prop :=
  ¬IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D r b).command

private theorem cut_free_header (P : Parameters) (D : Plan P) (r : List Bool) (b : ℕ)
    (h : (IntegralMixedCommandHeaderBits.command
      (IntegralMixedFramedRootPullback.instructionAt P D r b).command).context<2) : CutFreeAt P D r b := by
  intro HC
  have HH := (IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context] at HH
  omega

private theorem no_cut_stages (P : Parameters) (D : Plan P) (r w : List Bool) (m : ℕ)
    (hm : (D.rules r).length=m) (h : ∀b<m,CutFreeAt P D r b) :
    ∀j<m-1,IntegralFramedTraceCutScan.StageCut P D (IntegralFramedTraceCutScan.stagePacket (pair r w) j)→False := by
  intro j hj HC
  have HJ : j<IntegralFramedTraceCutMetadata.length P D (pairFst (pair r w))+1 := by
    change j<(D.rules (pairFst (pair r w))).length+1
    rw [pairFst_pair,hm]
    omega
  have HD := (IntegralFramedTraceCutOrigin.stageCut_iff P D (pair r w) j HJ).mp HC
  rw [pairFst_pair] at HD
  exact h j (by omega) HD

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
private theorem before_shape (q : List Bool) : FormulaSignSlotRadialProviderAtomic.Cuts.holds q ↔
    ∀j<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)-1,
      IntegralFramedTraceCutScan.StageCut P D (IntegralFramedTraceCutScan.stagePacket q j)→
        FormulaSignSlotRadialProviderAtomic.Cuts.Guards (IntegralFramedTraceCutScan.stagePacket q j) := Iff.rfl

private theorem stageHeader_shape (r : List Bool) (b : ℕ) : stageHeader r b=
    IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D r b).command := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source stageHeader CutFreeAt
  IntegralFramedTraceCutScan.StageCut FormulaSignSlotRadialProviderAtomic.Cuts.StageCut
  FormulaSignSlotRadialProviderAtomic.Cuts.Guards FormulaSignSlotRadialProviderAtomic.Cuts.holds
  IntegralMixedFramedRootPullback.instructionAt

private theorem holds_from_no_cut (r w : List Bool)
    (hl : ((D).rules r).length=FormulaSignSlotRadialProviderRecordPlan.fullCount r)
    (H : ∀b<FormulaSignSlotRadialProviderRecordPlan.fullCount r,CutFreeAt P D r b) :
    FormulaSignSlotRadialProviderAtomic.Cuts.holds (pair r w) := by
  apply (before_shape (pair r w)).mpr
  intro j hj HC
  have HB : j<FormulaSignSlotRadialProviderRecordPlan.fullCount r-1 := by
    simpa only [pairFst_pair] using hj
  exact False.elim (no_cut_stages P D r w (FormulaSignSlotRadialProviderRecordPlan.fullCount r) hl H j HB HC)

theorem no_cut (c : List Bool) (b : ℕ) (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount (root c)) :
    CutFreeAt P D (root c) b := by
  have HH : (stageHeader (root c) b).context<2 := by
    by_cases hi : b<FormulaSignSlotRadialProviderRecordPlan.count (root c)
    · rw [integer_header _ _ hi]
      decide
    · have HL : b=FormulaSignSlotRadialProviderRecordPlan.count (root c)+
          (b-FormulaSignSlotRadialProviderRecordPlan.count (root c)) := by omega
      have HA : b-FormulaSignSlotRadialProviderRecordPlan.count (root c)<IntegralMixedCausalRecordPlanBits.count (root c) := by
        unfold FormulaSignSlotRadialProviderRecordPlan.fullCount at hb
        omega
      rw [HL,critical_header c _ HA]
      exact Nat.lt_succ_self 1
  exact cut_free_header P D (root c) b
    ((congrArg (fun H : IntegralMixedCommandHeaderBits.Header=>H.context<2) (stageHeader_shape (root c) b)).mp HH)

theorem before_probe (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (pair (root c) []) w) :
    FormulaSignSlotRadialProviderAtomic.BeforeProbe (packet c w) := by
  refine ⟨?_,?_⟩
  · simpa only [FormulaSignSlotRadialProviderAtomic.FullValid,context_packet,word_packet] using hw
  · simp only [FormulaSignSlotRadialProviderAtomic.fullQuery,root_packet,word_packet]
    exact holds_from_no_cut (root c) w (full_length c) (no_cut c)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
