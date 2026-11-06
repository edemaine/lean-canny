/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendTail
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedMidpoint
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedChild
/-! # Actual proper-level clocks include every fresh endpoint record -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem append_fresh_count (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool) :
    IntegralMixedRoadmapChain.freshCount (IntegralMixedRoadmapChain.appendPayload n q l r side p)
      (IntegralMixedRoadmapChain.depth q)=
        IntegralMixedRoadmapEndpointSyntax.fresh l+IntegralMixedRoadmapEndpointSyntax.fresh r := by
  simp [IntegralMixedRoadmapChain.freshCount,IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,
    IntegralMixedRoadmapChain.append_entry_last,IntegralMixedRoadmapChain.levelEntry,WordList.get_encode]

private theorem end_birth_same (d n : ℕ) (q : List Bool) :
    IntegralMixedRoadmapAtomic.endBirth d n q=FormulaSignSlotRadialProviderAtomic.endBirth d n q := rfl

variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right)
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old
local notation "K" => D-FormulaSignSlotRadialProviderAtomic.depth old
local notation "q" side => packet D old R.leftSpec R.rightSpec side []

noncomputable def midpointBirth := beginBirth old+R.result.commands.length

theorem fresh_count : R.result.commands.length=
    IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec+IntegralMixedRoadmapEndpointSyntax.fresh R.rightSpec :=
  R.count.trans (congrArg₂ (·+·) R.left_fresh R.right_fresh).symm

theorem finish_eq (side : Bool) : finishBirth old hv hd left right R side=
    midpointBirth old hv hd left right R+2+2*K := by
  unfold finishBirth midpointBirth
  rw [level_code_count,←fresh_count old hv hd left right R]
  omega

theorem plain_payload (side : Bool) : IntegralMixedRoadmapAtomic.payload (q side)=
    payload D old R.leftSpec R.rightSpec side := payload_packet _ _ _ _ _ _

theorem plain_depth (side : Bool) : IntegralMixedRoadmapAtomic.depth (q side)=
    FormulaSignSlotRadialProviderAtomic.depth old+1 := depth_packet _ _ _ _ _ _

theorem packet_level (side : Bool) : IntegralMixedRoadmapProper.levelIndex (q side)=
    FormulaSignSlotRadialProviderAtomic.depth old := by
  simp only [IntegralMixedRoadmapProper.levelIndex,plain_depth,Nat.add_sub_cancel]

theorem fresh_last (side : Bool) : IntegralMixedRoadmapChain.freshCount
    (payload D old R.leftSpec R.rightSpec side) (FormulaSignSlotRadialProviderAtomic.depth old)=
      R.result.commands.length := by
  rw [fresh_count]
  simpa only [payload,FormulaSignSlotRadialProviderAtomic.depth] using append_fresh_count D
    (FormulaSignSlotRadialProviderAtomic.payload old) R.leftSpec R.rightSpec side
    (IntegralMixedRoadmapChain.seedCode D)

theorem midpoint_birth (side : Bool) : IntegralMixedRoadmapProper.midBirth D N (q side)=
    midpointBirth old hv hd left right R := by
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth IntegralMixedRoadmapChain.birth
  rw [plain_payload,packet_level,pair_start old hv hd left right R side,fresh_last]
  unfold midpointBirth
  rw [begin_eq_start]

theorem midpoint_count (side : Bool) : IntegralMixedRoadmapProper.captureCount D (q side)=K := by
  simp only [IntegralMixedRoadmapProper.captureCount,packet_level]

theorem child_count (side : Bool) : IntegralMixedRoadmapAtomic.free D (q side)=K := by
  unfold IntegralMixedRoadmapAtomic.free
  rw [plain_depth]
  omega

theorem packet_end_birth (side : Bool) : IntegralMixedRoadmapAtomic.endBirth D N (q side)=
    finishBirth old hv hd left right R side := by
  have H := end_birth old hv hd left right R side []
  rw [dimension_packet,initial_packet] at H
  exact (end_birth_same D N (q side)).trans H

theorem child_anchor (side : Bool) : IntegralMixedRoadmapAtomic.anchor D N (q side)=
    midpointBirth old hv hd left right R+1+K := by
  unfold IntegralMixedRoadmapAtomic.anchor
  rw [packet_end_birth,child_count,finish_eq]
  omega

theorem midpoint_lt_finish (side : Bool) : midpointBirth old hv hd left right R<finishBirth old hv hd left right R side := by
  rw [finish_eq]
  omega

theorem midpoint_lt_full (side : Bool) : midpointBirth old hv hd left right R<fullBirth old hv hd left right R side :=
  (midpoint_lt_finish old hv hd left right R side).trans_le (finish_le_full old hv hd left right R side)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
