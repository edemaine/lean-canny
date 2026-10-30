/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSweepGeometry
public import LeanCanny.Encoding.CoordinateDoubleAffineSweepSamples

/-! # The computed sweep parent word names the original source slice

The conversion preserves the odd-power decoded ancestor tuple as well as the
power point. Consequently the actual coarse domain named by the computed
word is precisely the original slice, including singular frozen parents.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSweep
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleCompleteVertices.Valid

theorem parentWord_root (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (parentInput P depth old level) u w) :
    FlatAffineCompleteVertices.vertexEquiv (inputs P depth old level)
        (CoordinateDoubleAffinePrefix.coneCertificate P depth (objective depth old) level) u
        ⟨parentWord P depth old level (LeanCanny.pair u w), parentWord_valid P depth old level u w hw⟩ =
      parent P depth old level u
        (FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
          (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u ⟨w, hw⟩) := by
  have HP := parentWord_point P depth old level u w hw
  apply Subtype.ext
  change FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs P depth old level) u)
      ((SquareSampleCompleteVertices.candidate (sweepInput P depth old level) u
        (parentWord P depth old level (LeanCanny.pair u w)) (parentWord_valid P depth old level u w hw)).val ∘ Fin.castSucc) =
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs P depth old level) u)
      ((SquareSampleCompleteVertices.candidate (parentInput P depth old level) u w hw).val ∘ Fin.castSucc)
  exact congrArg (fun z : Fin (FlatAffineFullSourcePositive.count (CoordinateDoubleAffinePrefix.inputs P depth old level) u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs P depth old level) u) (z ∘ Fin.castSucc)) HP

theorem parentWord_coarse_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (hw : SquareSampleCompleteVertices.Valid (parentInput P depth old level) u w) :
    FlatAffineShiftedSlice.coarseSlice (inputs P depth old level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs P depth old level)
          (CoordinateDoubleAffinePrefix.coneCertificate P depth (objective depth old) level) u
          ⟨parentWord P depth old level (LeanCanny.pair u w), parentWord_valid P depth old level u w hw⟩)
        (CoordinateAffineTower.selected P old u (depth u)) =
      FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
        (FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
          (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u ⟨w, hw⟩) :=
  (congrArg (fun x => FlatAffineShiftedSlice.coarseSlice (inputs P depth old level) u x
      (CoordinateAffineTower.selected P old u (depth u))) (parentWord_root P depth old level u w hw)).trans
    (coarse_slice P depth old level u hn _)

end LeanCanny.Encoding.CoordinateDoubleAffineSweep
