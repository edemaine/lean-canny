/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointRoots
public import LeanCanny.Encoding.CoordinateDoubleAffineChildEquations
public import LeanCanny.Encoding.FlatAffineCompleteRootValues
public import LeanCanny.Algebra.FlatAffinePowerAppendPoint

/-! # The constructed midpoint child has the exact original slice

Its parent is the shared original parent. Its two retained coordinates are
exactly the coordinates of the original left and right critical samples.
The child therefore imposes the intended midpoint equation on that slice.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] midpointRoot midpointPrefixRoot originalParent parent

theorem midpointRoot_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    (midpointRoot P depth old level u left right hshared).val =
      FlatAffineTowerRegularity.appendPoint (depth u + 1) (midpointPrefixRoot P depth old level u left).val
        (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val) := by
  unfold midpointRoot
  exact FlatAffineCompleteRootStages.extend_val (midpointPrefix P depth old level) u
    (midpointPrefixRoot P depth old level u left)
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    (midpoint_right_stage P depth old level u left right hshared)

theorem midpointRoot_parent (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    parent true P depth old level u (midpointRoot P depth old level u left right hshared) =
      originalParent P depth old level u left := by
  have HV := congrArg (fun z : Fin ((depth u + 2) * FlatAffineCriticalTower.width (P.dim u + 4)) → ℝ =>
    z ∘ TriangularPolynomialRows.prefixIndex (FlatAffineCriticalTower.width (P.dim u + 4)) (depth u) (depth u + 2) (by omega))
    (midpointRoot_val P depth old level u left right hshared)
  apply Subtype.ext
  exact (parent_val true P depth old level u (midpointRoot P depth old level u left right hshared)).trans
    (HV.trans ((FlatAffineTowerRegularity.appendPoint_prefix_of_le (n := P.dim u + 4) (by omega : depth u ≤ depth u + 1)
      (midpointPrefixRoot P depth old level u left).val
      (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)).trans
        (midpoint_prefix_parent_val P depth old level u left).symm))

theorem midpointRoot_left_coordinate (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    retainedCoordinate P depth old u (depth u + 2) ⟨depth u, by omega⟩ (midpointRoot P depth old level u left right hshared).val =
      retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ left.val := by
  have HV := congrArg (retainedCoordinate P depth old u (depth u + 2) ⟨depth u, by omega⟩)
    (midpointRoot_val P depth old level u left right hshared)
  have HL := congrArg (retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩)
    (midpointPrefixRoot_val P depth old level u left)
  exact HV.trans ((FlatAffineTowerRegularity.appendPoint_old_block (n := P.dim u + 4) (k := depth u + 1)
    (midpointPrefixRoot P depth old level u left).val
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    ⟨depth u, by omega⟩ (Sum.inl (coordinateFin P depth old u))).trans HL)

theorem midpointRoot_right_coordinate (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    retainedCoordinate P depth old u (depth u + 2) ⟨depth u + 1, by omega⟩ (midpointRoot P depth old level u left right hshared).val =
      retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ right.val := by
  have HV := congrArg (retainedCoordinate P depth old u (depth u + 2) ⟨depth u + 1, by omega⟩)
    (midpointRoot_val P depth old level u left right hshared)
  exact HV.trans (FlatAffineTowerRegularity.appendPoint_new (depth u + 1)
    (midpointPrefixRoot P depth old level u left).val
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    (Sum.inl (coordinateFin P depth old u)))

theorem midpointRoot_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u left = originalParent P depth old level u right) :
    FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u
        (midpointRoot P depth old level u left right hshared) =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
          (originalParent P depth old level u left) ∧ 2 * y (coordinateFin P depth old u) =
        retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ left.val +
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ right.val} := by
  have HV := congrArg₂ (fun a b : ℝ => a + b) (midpointRoot_left_coordinate P depth old level u left right hshared)
    (midpointRoot_right_coordinate P depth old level u left right hshared)
  exact (slice_midpoint P depth old level u hn (midpointRoot P depth old level u left right hshared)).trans
    (congrArg₂ (fun x v => {y | y ∈ FlatAffineCompleteComponentSamples.slice
      (CoordinateDoubleAffinePrefix.inputs P depth old level) u x ∧ 2 * y (coordinateFin P depth old u) = v})
      (midpointRoot_parent P depth old level u left right hshared) HV)

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
