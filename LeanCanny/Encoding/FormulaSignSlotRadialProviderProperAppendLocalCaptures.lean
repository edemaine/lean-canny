/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendMidpointCompanions
/-! # Original free-coordinate captures are the actual MID and child coordinates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor

private theorem capture_field_at_context (q : List Bool) (hq : FormulaSignSlotRadialProviderAtomic.Valid q)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (hc : FormulaSignSlotRadialProviderAtomic.context q=c) (hword : FormulaSignSlotRadialProviderAtomic.word q=w) (b : ℕ) :
    FormulaSignSlotRadialProviderAtomic.field q hq b=FormulaSignSlotRadialProviderAtomic.bankField c w hw b := by
  cases hc
  cases hword
  rfl

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "mid" => midpointBirth old hv hd left right R
local notation "K" => dimension old-depth old
local notation "q" => packet (dimension old) old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

theorem SampledLevel.original_capture_fields (S : SampledLevel old hv hd left right R side pMID pChild)
    (j : ℕ) (hj : depth old+1≤j) (hjn : j≤dimension old) :
    ∃ij : Fin ((P).ambient c+1),ij.val=j ∧
      FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
        (IntegralMixedRoadmapProper.midProducer (dimension (q S.receipt.word))
          (FormulaSignSlotRadialProviderAtomic.initial (q S.receipt.word)) (q S.receipt.word) j)=pMID ij ∧
      FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
        (IntegralMixedRoadmapProper.childProducer (dimension (q S.receipt.word))
          (FormulaSignSlotRadialProviderAtomic.initial (q S.receipt.word)) (q S.receipt.word) j)=pChild ij := by
  have HD : (P).ambient c=dimension old := FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  let ij : Fin ((P).ambient c+1) := ⟨j,by omega⟩
  let i := dimension old-j
  have HI : i<K := by dsimp only [i];omega
  have HF := finish_eq old hv hd left right R side
  have HMid0 : mid≤mid+1+i := by omega
  have HMid1 : mid+1+i<finishBirth old hv hd left right R side := by omega
  have HChild0 : mid≤mid+1+K+1+i := by omega
  have HChild1 : mid+1+K+1+i<finishBirth old hv hd left right R side := by omega
  have HMidPhase : mid+1+i<mid+1+K := by omega
  have HChildPhase : ¬mid+1+K+1+i<mid+1+K := by omega
  have HMid := S.local_correlation (mid+1+i) HMid0 HMid1
  have HChild := S.local_correlation (mid+1+K+1+i) HChild0 HChild1
  simp only [ite_eq_left HMidPhase] at HMid
  simp only [ite_eq_right HChildPhase] at HChild
  have HMidSel : FormulaSignSlotRadialProviderAtomic.selected (C r) (mid+1+i)=j := by
    have HS := (midpoint_capture_metadata old hv hd left right R side i HI).2
    exact HS.trans (by dsimp only [i];omega)
  have HChildSel : FormulaSignSlotRadialProviderAtomic.selected (C r) (mid+1+K+1+i)=j := by
    have HClock : mid+1+K+1+i=mid+2+K+i := by omega
    rw [HClock]
    have HS := (child_capture_metadata old hv hd left right R side i HI).2
    exact HS.trans (by dsimp only [i];omega)
  have HM : FormulaSignSlotRadialProviderAtomic.bankField (C r) S.receipt.word S.receipt.valid (mid+1+i)=pMID ij :=
    HMid.trans (nativePoint_value old hv hd left right R side pMID _ ij HMidSel)
  have HC : FormulaSignSlotRadialProviderAtomic.bankField (C r) S.receipt.word S.receipt.valid (mid+1+K+1+i)=pChild ij :=
    HChild.trans (nativePoint_value old hv hd left right R side pChild _ ij HChildSel)
  have HMB : IntegralMixedRoadmapProper.midProducer (dimension (q S.receipt.word))
      (FormulaSignSlotRadialProviderAtomic.initial (q S.receipt.word)) (q S.receipt.word) j=mid+1+i := by
    unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst
    rw [midpoint_birth_packet old hv hd left right R side S.receipt.word,dimension_packet]
  have HCB : IntegralMixedRoadmapProper.childProducer (dimension (q S.receipt.word))
      (FormulaSignSlotRadialProviderAtomic.initial (q S.receipt.word)) (q S.receipt.word) j=mid+1+K+1+i := by
    unfold IntegralMixedRoadmapProper.childProducer IntegralMixedRoadmapAtomic.first
    rw [dimension_packet,initial_packet,latest_anchor_packet old hv hd left right R side S.receipt.word]
  refine ⟨ij,rfl,?_,?_⟩
  · rw [HMB]
    exact (capture_field_at_context _ S.atomic_valid (C r) S.receipt.word S.receipt.valid
      (context_packet old R.leftSpec R.rightSpec side S.receipt.word) (word_packet _ _ _ _ _ _) _).trans HM
  · rw [HCB]
    exact (capture_field_at_context _ S.atomic_valid (C r) S.receipt.word S.receipt.valid
      (context_packet old R.leftSpec R.rightSpec side S.receipt.word) (word_packet _ _ _ _ _ _) _).trans HC

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
