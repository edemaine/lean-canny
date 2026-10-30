/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildEquations
public import LeanCanny.Encoding.CoordinateDoubleAffineChildSamples

/-! # Computed parent words recover the original recursive slice

The native projected parent word decodes to exactly the retained original
parent, including every multiplier. The fixed-height and midpoint domain
identities therefore use the actual computed word in the original sampler.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleCompleteVertices.Valid parent

theorem powerPoint_projection (F : FlatAffineFullSourceTower.Inputs) (d : List Bool → ℕ)
    (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ) :
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u)
        ((z ∘ FlatAffinePowerPrefix.projection F d hd u) ∘ Fin.castSucc) =
      FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z ∘ Fin.castSucc) ∘
        TriangularPolynomialRows.prefixIndex (FlatAffineFullSourceTower.stageWidth F u) (d u) (F.depth u) (hd u) := by
  have H : (z ∘ FlatAffinePowerPrefix.projection F d hd u) ∘ Fin.castSucc =
      (z ∘ Fin.castSucc) ∘ FlatAffinePowerTower.prefixIndex (hd u) := by
    funext i
    exact congrArg z (FlatAffinePowerPrefix.projection_old F d hd u i)
  exact (congrArg (FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u)) H).trans
    (FlatAffinePowerTower.powerPoint_prefix (hd u) (FlatAffinePowerControls.degree F u) (z ∘ Fin.castSucc))

theorem parentWord_root (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (childInput midpoint P depth old level) u w) :
    FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
        (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u
        ⟨parentWord midpoint P depth old level (LeanCanny.pair u w), parentWord_valid midpoint P depth old level u w hw⟩ =
      parent midpoint P depth old level u
        (FlatAffineCompleteVertices.vertexEquiv (inputs midpoint P depth old level) (cone midpoint P depth old level) u ⟨w, hw⟩) := by
  have HP := parentWord_point midpoint P depth old level u w hw
  have HE := congrArg (fun z : Fin ((parentInput P depth old level).count u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs midpoint P depth old level) u) (z ∘ Fin.castSucc)) HP
  apply Subtype.ext
  exact HE.trans ((powerPoint_projection (inputs midpoint P depth old level) depth (child_depth_le midpoint depth) u
    (SquareSampleCompleteVertices.candidate (childInput midpoint P depth old level) u w hw).val).trans
      (parent_val midpoint P depth old level u
        (FlatAffineCompleteVertices.vertexEquiv (inputs midpoint P depth old level) (cone midpoint P depth old level) u ⟨w, hw⟩)).symm)

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
