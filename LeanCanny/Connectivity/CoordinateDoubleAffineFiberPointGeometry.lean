/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalFiberPairs
public import Mathlib.Tactic.Linarith

/-! # Retained point pairs in the actual common-height fiber

A midpoint child retains the complete spatial points of both critical roots.
When the native height-equality guard accepts, its slice is the actual common
height fiber. Thus point-to-point connection queries can reference retained
stages rather than assuming that these points are critical for the next
objective. No path-connectedness assumption on a singular fiber is used.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineFiberPointGeometry
open Set LeanCanny.Algebra LeanCanny.Encoding
open CoordinateDoubleAffineChildRecords
open scoped Classical

def retainedPoint (n m : ℕ) (t : Fin m)
    (z : Fin (m * FlatAffineCriticalTower.width n) → ℝ) : Fin n → ℝ := fun i =>
  z (TriangularPolynomialRows.block (FlatAffineCriticalTower.width n) t.val m t.isLt
    (FlatAffineCriticalTower.blockEquiv n (Sum.inl i)))

theorem midpointRoot_left_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hs : originalParent P depth old level u left = originalParent P depth old level u right) :
    retainedPoint (P.dim u + 4) (depth u + 2) ⟨depth u, by omega⟩
      (midpointRoot P depth old level u left right hs).val =
        FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u left.val ∘ Sum.inl := by
  funext i
  have H := congrArg (fun z => retainedPoint (P.dim u + 4) (depth u + 2)
    ⟨depth u, by omega⟩ z i) (midpointRoot_val P depth old level u left right hs)
  have HL := congrArg (fun z => retainedPoint (P.dim u + 4) (depth u + 1)
    ⟨depth u, by omega⟩ z i) (midpointPrefixRoot_val P depth old level u left)
  exact H.trans ((FlatAffineTowerRegularity.appendPoint_old_block (n := P.dim u + 4)
    (k := depth u + 1) (midpointPrefixRoot P depth old level u left).val
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    ⟨depth u, by omega⟩ (Sum.inl i)).trans HL)

theorem midpointRoot_right_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (left right : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hs : originalParent P depth old level u left = originalParent P depth old level u right) :
    retainedPoint (P.dim u + 4) (depth u + 2) ⟨depth u + 1, by omega⟩
      (midpointRoot P depth old level u left right hs).val =
        FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val ∘ Sum.inl := by
  funext i
  have H := congrArg (fun z => retainedPoint (P.dim u + 4) (depth u + 2)
    ⟨depth u + 1, by omega⟩ z i) (midpointRoot_val P depth old level u left right hs)
  exact H.trans (FlatAffineTowerRegularity.appendPoint_new (depth u + 1)
    (midpointPrefixRoot P depth old level u left).val
    (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u right.val)
    (Sum.inl i))

namespace Pair
open CoordinateDoubleAffineCriticalPairs (input memberRoot midpointRoot midpointWord)

noncomputable def point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) : Fin (P.dim u + 4) → ℝ :=
  FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u
    (memberRoot P depth old level right u w hw).val ∘ Sum.inl

noncomputable def fiber (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) : Set (Fin (P.dim u + 4) → ℝ) :=
  {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
      (originalParent P depth old level u (memberRoot P depth old level false u w hw)) ∧
    y (coordinateFin P depth old u) = point P depth old level false u w hw (coordinateFin P depth old u)}

theorem midpoint_slice_eq_fiber (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage P depth old level)
    (hh : LeanCanny.pair u w ∈ CoordinateDoubleAffineCriticalFiberPairs.language P depth old level) :
    FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u
      (midpointRoot P depth old level u w hw hs) = fiber P depth old level u w hw := by
  rw [CoordinateDoubleAffineCriticalPairs.midpoint_slice P depth old level u w hn hw hs]
  have he := (CoordinateDoubleAffineCriticalFiberPairs.packet P depth old level u w hw).mp hh
  ext y
  change (_ ∧ 2 * _ = _ + _) ↔ (_ ∧ _ = _)
  change (_ ∧ 2 * y (coordinateFin P depth old u) =
    retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩
      (memberRoot P depth old level false u w hw).val +
    retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩
      (memberRoot P depth old level true u w hw).val) ↔
    (_ ∧ y (coordinateFin P depth old u) =
    retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩
      (memberRoot P depth old level false u w hw).val)
  constructor
  · rintro ⟨hy, ht⟩
    exact ⟨hy, by linarith⟩
  · rintro ⟨hy, ht⟩
    exact ⟨hy, by linarith⟩

theorem midpointWord_joined_iff (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ CoordinateDoubleAffineCriticalPairs.sharedLanguage P depth old level)
    (hh : LeanCanny.pair u w ∈ CoordinateDoubleAffineCriticalFiberPairs.language P depth old level) :
    let root := FlatAffineCompleteVertices.vertexEquiv (inputs true P depth old level) (cone true P depth old level) u
      ⟨midpointWord P depth old level (LeanCanny.pair u w),
        CoordinateDoubleAffineCriticalPairs.midpointWord_valid P depth old level u w hw hs⟩
    JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u root)
      (retainedPoint (P.dim u + 4) (depth u + 2) ⟨depth u, by omega⟩ root.val)
      (retainedPoint (P.dim u + 4) (depth u + 2) ⟨depth u + 1, by omega⟩ root.val) ↔
      JoinedIn (fiber P depth old level u w hw)
        (point P depth old level false u w hw) (point P depth old level true u w hw) := by
  dsimp only
  rw [CoordinateDoubleAffineCriticalPairs.midpointWord_root P depth old level u w hw hs,
    midpoint_slice_eq_fiber P depth old level u w hn hw hs hh]
  unfold CoordinateDoubleAffineCriticalPairs.midpointRoot
  rw [midpointRoot_left_point, midpointRoot_right_point]
  rfl

end Pair
end LeanCanny.Connectivity.CoordinateDoubleAffineFiberPointGeometry
