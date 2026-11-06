/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendClocks
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalMetadata
/-! # Actual native MID and child headers after all fresh endpoint cuts -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open FormulaSignSlotRadialProviderRecordPrefix (context)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "q" => packet (dimension old) old R.leftSpec R.rightSpec side []
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side

private theorem initial_le_midpoint : N old≤midpointBirth old hv hd left right R := by
  unfold midpointBirth
  rw [begin_eq_start]
  omega

private theorem packet_checked :
    IntegralMixedRoadmapChain.Checked (dimension old) (FormulaSignSlotRadialProviderAtomic.width old)
      (FormulaSignSlotRadialProviderAtomic.sourceCap old) (N old) (FormulaSignSlotRadialProviderAtomic.width old)
      (IntegralMixedRoadmapAtomic.payload q) := by
  rw [plain_payload]
  exact checked old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)

private theorem packet_positive : 0<IntegralMixedRoadmapAtomic.depth q := by
  rw [plain_depth]
  omega

private theorem packet_code (i : ℕ) : IntegralMixedCausalRecordPlanBits.code r i=
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) i := by
  unfold IntegralMixedCausalRecordPlanBits.code preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_records]
  rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source preparedRoot start
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

private theorem frame_record_metadata (b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth old hv hd left right R side) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood (dimension old) b labels g j)
    (hc : WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q))
      (b-N old)=IntegralMixedChronologicalFrameCode.code (dimension old) labels g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) b=j := by
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count r+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count r := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count r+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient r)
      (FormulaSignSlotRadialProviderRecordPlan.count r+i) labels g j :=
    Eq.mp (congrArg₂ (fun n b=>IntegralMixedChronologicalFrameCode.PointGood n b labels g j)
      (prepared_dimension old R.leftSpec R.rightSpec side).symm HB) hg
  have HC : IntegralMixedCausalRecordPlanBits.code r i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient r) labels g j := by
    rw [packet_code,prepared_dimension]
    exact hc
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.frame_metadata r i HI labels g j HG HC
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context r)) HB).trans H.2⟩

private theorem midpoint_record_metadata (b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth old hv hd left right R side) (labels : List Bool) (a c g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good (dimension old) b labels a c g j)
    (hc : WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q))
      (b-N old)=IntegralMixedChronologicalMidpointCode.code (dimension old) labels a c g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) b=j := by
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count r+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count r := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count r+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG : IntegralMixedChronologicalMidpointCode.Good ((P).ambient r)
      (FormulaSignSlotRadialProviderRecordPlan.count r+i) labels a c g j :=
    Eq.mp (congrArg₂ (fun n b=>IntegralMixedChronologicalMidpointCode.Good n b labels a c g j)
      (prepared_dimension old R.leftSpec R.rightSpec side).symm HB) hg
  have HC : IntegralMixedCausalRecordPlanBits.code r i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient r) labels a c g j := by
    rw [packet_code,prepared_dimension]
    exact hc
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.midpoint_metadata r i HI labels a c g j HG HC
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context r) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context r)) HB).trans H.2⟩

include hv hd in
theorem midpoint_anchor_metadata :
    FormulaSignSlotRadialProviderAtomic.Active (context r) (midpointBirth old hv hd left right R) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) (midpointBirth old hv hd left right R)=depth old+1 := by
  have HN := initial_le_midpoint old hv hd left right R
  have HEfull := finish_eq old hv hd left right R side
  have H := packet_checked old hv hd left right R side
  have HF := finish_le_full old hv hd left right R side
  have HB := midpoint_birth old hv hd left right R side
  have HG := IntegralMixedRoadmapProper.checked_midpoint_good H (packet_positive old hv hd left right R side)
  have HC := IntegralMixedRoadmapProper.checked_midpoint_record H (packet_positive old hv hd left right R side)
  have HI : IntegralMixedRoadmapProper.midBirth (dimension old) (N old) q-N old=
      IntegralMixedRoadmapProper.midRawIndex (dimension old) q := by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM := midpoint_record_metadata old hv hd left right R side _ (by rw [HB];omega)
    (by rw [HB];have HE := midpoint_lt_finish old hv hd left right R side;omega) _ _ _ _ _ HG (by rw [HI];exact HC)
  simpa only [HB,packet_level] using HM

include hv hd in
theorem midpoint_capture_metadata (i : ℕ) (hi : i<dimension old-depth old) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) (midpointBirth old hv hd left right R+1+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) (midpointBirth old hv hd left right R+1+i)=dimension old-i := by
  have HN := initial_le_midpoint old hv hd left right R
  have HEfull := finish_eq old hv hd left right R side
  have H := packet_checked old hv hd left right R side
  have HF := finish_le_full old hv hd left right R side
  have HB : IntegralMixedRoadmapProper.midFirst (dimension old) (N old) q+i=midpointBirth old hv hd left right R+1+i := by
    unfold IntegralMixedRoadmapProper.midFirst
    rw [midpoint_birth]
  have HI : i<IntegralMixedRoadmapProper.captureCount (dimension old) q := by rw [midpoint_count];exact hi
  have HG := IntegralMixedRoadmapProper.checked_midpoint_companion_good H (packet_positive old hv hd left right R side) i HI
  have HC := IntegralMixedRoadmapProper.checked_midpoint_companion_record H (packet_positive old hv hd left right R side) i HI
  have HR : IntegralMixedRoadmapProper.midFirst (dimension old) (N old) q+i-N old=
      IntegralMixedRoadmapProper.midRawIndex (dimension old) q+1+i := by
    unfold IntegralMixedRoadmapProper.midFirst IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM := midpoint_record_metadata old hv hd left right R side _ (by rw [HB];omega)
    (by rw [HB];have HE := midpoint_lt_finish old hv hd left right R side;omega) _ _ _ _ _ HG (by rw [HR];exact HC)
  simpa only [HB] using HM

include hv hd in
theorem child_anchor_metadata :
    FormulaSignSlotRadialProviderAtomic.Active (context r)
      (midpointBirth old hv hd left right R+1+(dimension old-depth old)) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r)
        (midpointBirth old hv hd left right R+1+(dimension old-depth old))=depth old+1 := by
  have HN := initial_le_midpoint old hv hd left right R
  have HEfull := finish_eq old hv hd left right R side
  have H := packet_checked old hv hd left right R side
  have HF := finish_le_full old hv hd left right R side
  have HB := child_anchor old hv hd left right R side
  have HG := IntegralMixedRoadmapAtomic.anchor_point_good H
  have HC := IntegralMixedRoadmapAtomic.checked_anchor_record H (packet_positive old hv hd left right R side)
  have HM := frame_record_metadata old hv hd left right R side _ (by rw [HB];omega)
    (by rw [HB];have HE := midpoint_lt_finish old hv hd left right R side;omega) _ _ _ HG HC
  simpa only [HB,plain_depth] using HM

include hv hd in
theorem child_capture_metadata (i : ℕ) (hi : i<dimension old-depth old) :
    FormulaSignSlotRadialProviderAtomic.Active (context r)
      (midpointBirth old hv hd left right R+2+(dimension old-depth old)+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r)
        (midpointBirth old hv hd left right R+2+(dimension old-depth old)+i)=dimension old-i := by
  have HN := initial_le_midpoint old hv hd left right R
  have HEfull := finish_eq old hv hd left right R side
  have H := packet_checked old hv hd left right R side
  have HF := finish_le_full old hv hd left right R side
  have HB : IntegralMixedRoadmapAtomic.first (dimension old) (N old) q+i=
      midpointBirth old hv hd left right R+2+(dimension old-depth old)+i := by
    unfold IntegralMixedRoadmapAtomic.first
    rw [child_anchor]
    omega
  have HI : i<IntegralMixedRoadmapAtomic.free (dimension old) q := by rw [child_count];exact hi
  have HG := IntegralMixedRoadmapAtomic.capture_point_good H i HI
  have HC := IntegralMixedRoadmapAtomic.latest_capture_record H i HI
  have HR : IntegralMixedRoadmapAtomic.first (dimension old) (N old) q+i-N old=
      IntegralMixedRoadmapAtomic.first (dimension old) (N old) q-N old+i := by rw [HB];omega
  have HM := frame_record_metadata old hv hd left right R side _ (by rw [HB];omega)
    (by rw [HB];have HE := midpoint_lt_finish old hv hd left right R side;omega) _ _ _ HG (by rw [HR];exact HC)
  simpa only [HB] using HM

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
