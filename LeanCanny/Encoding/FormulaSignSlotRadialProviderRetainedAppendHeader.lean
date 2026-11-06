/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendTail
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedMidpoint
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedChild
/-! # The retained MID and child stages have actual native critical headers -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open FormulaSignSlotRadialProviderRecordPrefix (context)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "Q" => (fun old e=>packet (dimension old) old e [])

private theorem plain_payload (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.payload (Q old e)=payload (dimension old) old e := payload_packet _ _ _ _
private theorem plain_depth (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.depth (Q old e)=depth old+1 := depth_packet _ _ _ _

private theorem packet_checked (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    IntegralMixedRoadmapChain.Checked (dimension old) (FormulaSignSlotRadialProviderAtomic.width old)
      (FormulaSignSlotRadialProviderAtomic.sourceCap old) (N old) (FormulaSignSlotRadialProviderAtomic.width old)
      (IntegralMixedRoadmapAtomic.payload (Q old e)) := by
  rw [plain_payload]
  exact checked old hv hd e he

private theorem packet_positive (old : List Bool) (e : ℕ) : 0<IntegralMixedRoadmapAtomic.depth (Q old e) := by
  rw [plain_depth]
  omega

private theorem packet_level (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapProper.levelIndex (Q old e)=depth old := by
  simp only [IntegralMixedRoadmapProper.levelIndex,plain_depth,Nat.add_sub_cancel]

theorem midpoint_birth (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapProper.midBirth (dimension old) (N old) (Q old e)=N old+start old := by
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth IntegralMixedRoadmapChain.birth
  rw [plain_payload,packet_level,fresh_last,raw_start_last]
  simp only [Nat.add_zero,start]

theorem midpoint_count (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapProper.captureCount (dimension old) (Q old e)=dimension old-depth old := by
  simp only [IntegralMixedRoadmapProper.captureCount,packet_level]

theorem child_count (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.free (dimension old) (Q old e)=dimension old-depth old := by
  simp only [IntegralMixedRoadmapAtomic.free,plain_depth,Nat.add_sub_add_right]

theorem begin_eq (old : List Bool) : endBirth (dimension old) (N old) old=N old+start old := by
  unfold start
  rfl

theorem child_anchor (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapAtomic.anchor (dimension old) (N old) (Q old e)=
      N old+start old+1+(dimension old-depth old) := by
  unfold IntegralMixedRoadmapAtomic.anchor
  change finishBirth old e-(_+1)=_
  rw [child_count,finish_eq,begin_eq]
  omega

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source preparedRoot start
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

private theorem frame_record_metadata (old : List Bool) (e b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth old e) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood (dimension old) b labels g j)
    (hc : WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload (Q old e)))
      (b-N old)=IntegralMixedChronologicalFrameCode.code (dimension old) labels g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e)) b=j := by
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (preparedRoot old e))
      (FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i) labels g j :=
    Eq.mp (congrArg₂ (fun n b=>IntegralMixedChronologicalFrameCode.PointGood n b labels g j)
      (prepared_dimension old e).symm HB) hg
  have HC : IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (preparedRoot old e)) labels g j := by
    rw [prepared_code,prepared_dimension,←plain_payload]
    exact hc
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.frame_metadata (preparedRoot old e) i HI labels g j HG HC
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e))) HB).trans H.2⟩

private theorem midpoint_record_metadata (old : List Bool) (e b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth old e) (labels : List Bool) (a c g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good (dimension old) b labels a c g j)
    (hc : WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload (Q old e)))
      (b-N old)=IntegralMixedChronologicalMidpointCode.code (dimension old) labels a c g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e)) b=j := by
  let i := b-N old
  have HB : b=FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i := by
    rw [prepared_initial]
    dsimp only [i]
    omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) := by
    change b<FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+_ at hb1
    rw [prepared_initial] at hb1
    dsimp only [i]
    omega
  have HG : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (preparedRoot old e))
      (FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+i) labels a c g j :=
    Eq.mp (congrArg₂ (fun n b=>IntegralMixedChronologicalMidpointCode.Good n b labels a c g j)
      (prepared_dimension old e).symm HB) hg
  have HC : IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (preparedRoot old e)) labels a c g j := by
    rw [prepared_code,prepared_dimension,←plain_payload]
    exact hc
  have H := FormulaSignSlotRadialProviderRecordCriticalMetadata.midpoint_metadata (preparedRoot old e) i HI labels a c g j HG HC
  exact ⟨Eq.mp (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) b) HB.symm) H.1,
    (congrArg (FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e))) HB).trans H.2⟩

variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (e : ℕ) (he : e<endBirth (dimension old) (N old) old)

private theorem begin_finish : N old+start old+2+2*(dimension old-depth old)=finishBirth old e := by
  rw [finish_eq,begin_eq]

include hv hd he in
theorem midpoint_anchor_metadata :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) (N old+start old) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e)) (N old+start old)=depth old+1 := by
  have H := packet_checked old hv hd e he
  have HF := finish_le_full old hv hd e he
  have HB := midpoint_birth old e
  have HG := IntegralMixedRoadmapProper.checked_midpoint_good H (packet_positive old e)
  have HC := IntegralMixedRoadmapProper.checked_midpoint_record H (packet_positive old e)
  have HI : IntegralMixedRoadmapProper.midBirth (dimension old) (N old) (Q old e)-N old=
      IntegralMixedRoadmapProper.midRawIndex (dimension old) (Q old e) := by
    unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM := midpoint_record_metadata old e _ (by rw [HB];omega)
    (by rw [HB];have HE := begin_finish old e;omega) _ _ _ _ _ HG (by rw [HI];exact HC)
  simpa only [HB,packet_level] using HM

include hv hd he in
theorem midpoint_capture_metadata (i : ℕ) (hi : i<dimension old-depth old) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e)) (N old+start old+1+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e)) (N old+start old+1+i)=dimension old-i := by
  have H := packet_checked old hv hd e he
  have HF := finish_le_full old hv hd e he
  have HB : IntegralMixedRoadmapProper.midFirst (dimension old) (N old) (Q old e)+i=N old+start old+1+i := by
    unfold IntegralMixedRoadmapProper.midFirst
    rw [midpoint_birth]
  have HI : i<IntegralMixedRoadmapProper.captureCount (dimension old) (Q old e) := by rw [midpoint_count];exact hi
  have HG := IntegralMixedRoadmapProper.checked_midpoint_companion_good H (packet_positive old e) i HI
  have HC := IntegralMixedRoadmapProper.checked_midpoint_companion_record H (packet_positive old e) i HI
  have HR : IntegralMixedRoadmapProper.midFirst (dimension old) (N old) (Q old e)+i-N old=
      IntegralMixedRoadmapProper.midRawIndex (dimension old) (Q old e)+1+i := by
    unfold IntegralMixedRoadmapProper.midFirst IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
      IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
    omega
  have HM := midpoint_record_metadata old e _ (by rw [HB];omega)
    (by rw [HB];have HE := begin_finish old e;omega) _ _ _ _ _ HG (by rw [HR];exact HC)
  simpa only [HB] using HM

include hv hd he in
theorem child_anchor_metadata :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e))
      (N old+start old+1+(dimension old-depth old)) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e))
        (N old+start old+1+(dimension old-depth old))=depth old+1 := by
  have H := packet_checked old hv hd e he
  have HF := finish_le_full old hv hd e he
  have HB := child_anchor old e
  have HG := IntegralMixedRoadmapAtomic.anchor_point_good H
  have HC := IntegralMixedRoadmapAtomic.checked_anchor_record H (packet_positive old e)
  have HM := frame_record_metadata old e _ (by rw [HB];omega)
    (by rw [HB];have HE := begin_finish old e;omega) _ _ _ HG HC
  simpa only [HB,plain_depth] using HM

include hv hd he in
theorem child_capture_metadata (i : ℕ) (hi : i<dimension old-depth old) :
    FormulaSignSlotRadialProviderAtomic.Active (context (preparedRoot old e))
      (N old+start old+2+(dimension old-depth old)+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context (preparedRoot old e))
        (N old+start old+2+(dimension old-depth old)+i)=dimension old-i := by
  have H := packet_checked old hv hd e he
  have HF := finish_le_full old hv hd e he
  have HB : IntegralMixedRoadmapAtomic.first (dimension old) (N old) (Q old e)+i=
      N old+start old+2+(dimension old-depth old)+i := by
    unfold IntegralMixedRoadmapAtomic.first
    rw [child_anchor]
    omega
  have HI : i<IntegralMixedRoadmapAtomic.free (dimension old) (Q old e) := by rw [child_count];exact hi
  have HG := IntegralMixedRoadmapAtomic.capture_point_good H i HI
  have HC := IntegralMixedRoadmapAtomic.latest_capture_record H i HI
  have HR : IntegralMixedRoadmapAtomic.first (dimension old) (N old) (Q old e)+i-N old=
      IntegralMixedRoadmapAtomic.first (dimension old) (N old) (Q old e)-N old+i := by rw [HB];omega
  have HM := frame_record_metadata old e _ (by rw [HB];omega)
    (by rw [HB];have HE := begin_finish old e;omega) _ _ _ HG (by rw [HR];exact HC)
  simpa only [HB] using HM

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
