/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildHeightSamples

/-! # The computed fixed-height child freezes its original critical sample -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] parent heightRoot

theorem parent_heightRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    parent false P depth old level u (heightRoot P depth old level u z) =
      FlatAffineCompleteRootStages.project
        (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
        depth u (by change depth u ≤ depth u + 1; omega) z := by
  have H := congrArg (fun x : Fin ((depth u + 1) * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ =>
    x ∘ TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4))
      (depth u) (depth u + 1) (by omega)) (heightRoot_val P depth old level u z)
  apply Subtype.ext
  exact (parent_val false P depth old level u (heightRoot P depth old level u z)).trans
    (H.trans (project_val (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
      depth u (by change depth u ≤ depth u + 1; omega) z).symm)

theorem heightRoot_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (z : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) :
    FlatAffineCompleteComponentSamples.slice (inputs false P depth old level) u (heightRoot P depth old level u z) =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
          (FlatAffineCompleteRootStages.project
            (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
            depth u (by change depth u ≤ depth u + 1; omega) z) ∧
        y (coordinateFin P depth old u) = retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ z.val} := by
  have HV := congrArg (retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩)
    (heightRoot_val P depth old level u z)
  exact (slice_height P depth old level u hn (heightRoot P depth old level u z)).trans
    (congrArg₂ (fun x v => {y | y ∈ FlatAffineCompleteComponentSamples.slice
      (CoordinateDoubleAffinePrefix.inputs P depth old level) u x ∧ y (coordinateFin P depth old u) = v})
      (parent_heightRoot P depth old level u z) HV)

theorem heightWord_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (criticalInput P depth old level) u w) :
    FlatAffineCompleteComponentSamples.slice (inputs false P depth old level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs false P depth old level) (cone false P depth old level) u
          ⟨heightWord P depth old level (LeanCanny.pair u w), heightWord_valid P depth old level u w hw⟩) =
      FlatAffineCompleteComponentSamples.slice (inputs false P depth old level) u
        (heightRoot P depth old level u
          (FlatAffineCompleteVertices.vertexEquiv
            (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
            (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) u ⟨w, hw⟩)) :=
  congrArg (FlatAffineCompleteComponentSamples.slice (inputs false P depth old level) u)
    (heightWord_root P depth old level u w hw)

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
