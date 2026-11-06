/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPacket
/-! # The actual proper child satisfies its complete latest companion scan -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem latest_free_packet (old l r : List Bool) (side : Bool) (w : List Bool) :
    IntegralMixedRoadmapAtomic.free (dimension old) (packet (dimension old) old l r side w)=dimension old-depth old := by
  unfold IntegralMixedRoadmapAtomic.free
  have HD : IntegralMixedRoadmapAtomic.depth (packet (dimension old) old l r side w)=depth old+1 := depth_packet _ _ _ _ _ _
  rw [HD]
  omega

section Clocks
variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "mid" => midpointBirth old hv hd left right R
local notation "K" => dimension old-depth old

theorem latest_anchor_packet (w : List Bool) :
    IntegralMixedRoadmapAtomic.anchor (dimension old) (N old)
      (packet (dimension old) old R.leftSpec R.rightSpec side w)=mid+1+K := by
  have HE : IntegralMixedRoadmapAtomic.endBirth (dimension old) (N old)
      (packet (dimension old) old R.leftSpec R.rightSpec side w)=finishBirth old hv hd left right R side := by
    have H := end_birth old hv hd left right R side w
    rw [dimension_packet,initial_packet] at H
    exact H
  unfold IntegralMixedRoadmapAtomic.anchor
  rw [HE,latest_free_packet,finish_eq]
  omega

theorem companion_query_packet (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (dimension (packet (dimension old) old R.leftSpec R.rightSpec side w))
      (N (packet (dimension old) old R.leftSpec R.rightSpec side w))
      (packet (dimension old) old R.leftSpec R.rightSpec side w)=
      LeanCanny.pair (LeanCanny.pair (C (preparedRoot old R.leftSpec R.rightSpec side)) w)
        (IntegralMixedPhysicalPointCompanionScan.descriptor (mid+1+K) (mid+1+K+1) K) := by
  rw [dimension_packet,initial_packet]
  unfold FormulaSignSlotRadialProviderAtomic.companionQuery FormulaSignSlotRadialProviderAtomic.first
    FormulaSignSlotRadialProviderAtomic.anchor FormulaSignSlotRadialProviderAtomic.free IntegralMixedRoadmapAtomic.first
  rw [sample_query_packet,latest_anchor_packet,latest_free_packet]
end Clocks

attribute [local irreducible] FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor

theorem SampledLevel.latest_companions
    {old : List Bool} {hv : A old} {hd : depth old<dimension old}
    {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
    {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (dimension (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word))
      (N (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word))
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)∈
      FormulaSignSlotRadialProviderAtomic.Companions.language := by
  rw [companion_query_packet old hv hd left right R side]
  let mid := midpointBirth old hv hd left right R
  let K := dimension old-depth old
  let r := preparedRoot old R.leftSpec R.rightSpec side
  let anchor := mid+1+K
  have HF := finish_eq old hv hd left right R side
  have HA := (child_anchor_metadata old hv hd left right R side).1
  have HFit : anchor+1+K≤prefixLength (B).parameters ((B).key (C r)) := by
    rw [FormulaSignSlotRadialProviderRecordPrefix.full_prefix]
    have H := finish_le_full old hv hd left right R side
    change finishBirth old hv hd left right R side≤FormulaSignSlotRadialProviderRecordPlan.fullCount r at H
    dsimp only [anchor,mid,K]
    omega
  apply (FormulaSignSlotRadialProviderAtomic.companion_language_packet_iff
    (C r) S.receipt.word S.receipt.valid anchor (anchor+1) K HA HFit).mpr
  have HAnchor0 : midpointBirth old hv hd left right R≤anchor := by dsimp only [anchor,mid,K];omega
  have HAnchor1 : anchor<finishBirth old hv hd left right R side := by dsimp only [anchor,mid,K];omega
  have HGAnchor : FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid anchor=
      nativePoint old hv hd left right R side pChild := by
    have H := S.local_geometric_point old hv hd left right R side anchor HAnchor0 HAnchor1
    simpa only [ite_eq_right (by dsimp only [anchor,mid,K];omega :
      ¬anchor<midpointBirth old hv hd left right R+1+(dimension old-depth old))] using H
  intro j hj
  have HJ0 : midpointBirth old hv hd left right R≤anchor+1+j := by dsimp only [anchor,mid,K];omega
  have HJ1 : anchor+1+j<finishBirth old hv hd left right R side := by dsimp only [anchor,mid,K] at *;omega
  have HJA := active_after_midpoint old hv hd left right R side _ HJ0
    (HJ1.trans_le (finish_le_full old hv hd left right R side))
  have HPhase : ¬anchor+1+j<midpointBirth old hv hd left right R+1+(dimension old-depth old) := by
    dsimp only [anchor,mid,K]
    omega
  refine ⟨HJA,?_,?_⟩
  · have H := S.local_geometric_point old hv hd left right R side (anchor+1+j) HJ0 HJ1
    have HG : FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid (anchor+1+j)=
        nativePoint old hv hd left right R side pChild := by simpa only [ite_eq_right HPhase] using H
    exact HG.trans HGAnchor.symm
  · rw [HGAnchor]
    simpa only [ite_eq_right HPhase] using S.local_correlation (anchor+1+j) HJ0 HJ1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
