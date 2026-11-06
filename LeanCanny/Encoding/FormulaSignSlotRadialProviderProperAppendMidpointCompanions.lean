/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperBase
/-! # The actual proper midpoint satisfies its complete companion scan -/
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

private theorem mid_plain_payload (q : List Bool) : IntegralMixedRoadmapAtomic.payload q=
    FormulaSignSlotRadialProviderAtomic.payload q := rfl
private theorem mid_plain_depth (q : List Bool) : IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q := rfl
private theorem mid_plain_sample (q : List Bool) : IntegralMixedRoadmapAtomic.sampleQuery q=
    FormulaSignSlotRadialProviderAtomic.sampleQuery q := rfl
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "mid" => midpointBirth old hv hd left right R
local notation "K" => dimension old-depth old
local notation "q" => packet (dimension old) old R.leftSpec R.rightSpec side

theorem midpoint_birth_packet (w : List Bool) :
    IntegralMixedRoadmapProper.midBirth (dimension (q w)) (N (q w)) (q w)=mid := by
  rw [dimension_packet,initial_packet]
  have HC : IntegralMixedRoadmapProper.midBirth (dimension old) (N old) (q w)=
      IntegralMixedRoadmapProper.midBirth (dimension old) (N old) (q []) := by
    simp only [IntegralMixedRoadmapProper.midBirth,IntegralMixedRoadmapProper.baseBirth,
      IntegralMixedRoadmapProper.levelIndex,mid_plain_depth,mid_plain_payload,depth_packet,payload_packet]
  exact HC.trans (midpoint_birth old hv hd left right R side)

theorem midpoint_query_packet (w : List Bool) :
    IntegralMixedRoadmapProper.midCompanions (dimension (q w)) (N (q w)) (q w)=
      LeanCanny.pair (LeanCanny.pair (C (preparedRoot old R.leftSpec R.rightSpec side)) w)
        (IntegralMixedPhysicalPointCompanionScan.descriptor mid (mid+1) K) := by
  unfold IntegralMixedRoadmapProper.midCompanions IntegralMixedRoadmapProper.midFirst
  rw [mid_plain_sample,sample_query_packet,midpoint_birth_packet]
  simp only [dimension_packet,IntegralMixedRoadmapProper.captureCount,IntegralMixedRoadmapProper.levelIndex,
    mid_plain_depth,depth_packet,Nat.add_sub_cancel]

variable {old hv hd left right R side}

theorem SampledLevel.midpoint_companions
    {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderProper.Midpoint (q S.receipt.word) := by
  change IntegralMixedRoadmapProper.midCompanions (dimension (q S.receipt.word)) (N (q S.receipt.word))
    (q S.receipt.word)∈FormulaSignSlotRadialProviderAtomic.Companions.language
  rw [midpoint_query_packet old hv hd left right R side]
  let r := preparedRoot old R.leftSpec R.rightSpec side
  have HA := (midpoint_anchor_metadata old hv hd left right R side).1
  have HF := finish_eq old hv hd left right R side
  have HFit : mid+1+K≤prefixLength (B).parameters ((B).key (C r)) := by
    rw [FormulaSignSlotRadialProviderRecordPrefix.full_prefix]
    have H := finish_le_full old hv hd left right R side
    change finishBirth old hv hd left right R side≤FormulaSignSlotRadialProviderRecordPlan.fullCount r at H
    omega
  apply (FormulaSignSlotRadialProviderAtomic.companion_language_packet_iff
    (C r) S.receipt.word S.receipt.valid mid (mid+1) K HA HFit).mpr
  have HAnchor : FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid mid=
      nativePoint old hv hd left right R side pMID := by
    have H := S.local_geometric_point old hv hd left right R side mid le_rfl (by omega)
    simpa only [ite_eq_left (by omega : mid<mid+1+K)] using H
  intro j hj
  have HJ0 : mid≤mid+1+j := by omega
  have HJ1 : mid+1+j<finishBirth old hv hd left right R side := by omega
  have HJA := active_after_midpoint old hv hd left right R side _ HJ0
    (HJ1.trans_le (finish_le_full old hv hd left right R side))
  have HPhase : mid+1+j<mid+1+K := by omega
  refine ⟨HJA,?_,?_⟩
  · have H := S.local_geometric_point old hv hd left right R side (mid+1+j) HJ0 HJ1
    have HG : FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid (mid+1+j)=
        nativePoint old hv hd left right R side pMID := by simpa only [ite_eq_left HPhase] using H
    exact HG.trans HAnchor.symm
  · rw [HAnchor]
    simpa only [ite_eq_left HPhase] using S.local_correlation (mid+1+j) HJ0 HJ1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
