/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointWords
public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairCompleteness
public import LeanCanny.Encoding.CoordinateDoubleAffineChildParentMatch

/-! # Exact slices, ancestry, and completeness of native midpoint children -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra
open CoordinateDoubleAffineChildRecords (inputs cone childInput originalParent retainedCoordinate coordinateFin)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberRoot midpointRoot midpointWord SquareSampleCompleteVertices.Valid

theorem midpointWord_parent (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    CoordinateDoubleAffineChildRecords.parent true P depth old level u
      (FlatAffineCompleteVertices.vertexEquiv (inputs true P depth old level) (cone true P depth old level) u
        ⟨midpointWord P depth old level (LeanCanny.pair u w), midpointWord_valid P depth old level u w hw hs⟩) =
      originalParent P depth old level u (memberRoot P depth old level false u w hw) := by
  have HE := congrArg (CoordinateDoubleAffineChildRecords.parent true P depth old level u)
    (midpointWord_root P depth old level u w hw hs)
  unfold midpointRoot at HE
  exact HE.trans (CoordinateDoubleAffineChildRecords.midpointRoot_parent P depth old level u
    (memberRoot P depth old level false u w hw) (memberRoot P depth old level true u w hw)
    (shared_originals P depth old level u w hw hs))

theorem midpointWord_parent_matches (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    LeanCanny.pair (LeanCanny.pair u (midpointWord P depth old level (LeanCanny.pair u w)))
        (parentWord P depth old level false (LeanCanny.pair u w)) ∈
      CoordinateDoubleAffineChildParentMatch.language true P depth old level := by
  apply (CoordinateDoubleAffineChildParentMatch.packet true P depth old level u
    (midpointWord P depth old level (LeanCanny.pair u w)) (parentWord P depth old level false (LeanCanny.pair u w))
    (midpointWord_valid P depth old level u w hw hs) (parentWord_valid P depth old level false u w hw)).mpr
  exact (midpointWord_parent P depth old level u w hw hs).trans (parentWord_root P depth old level false u w hw).symm

theorem midpointWord_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u
      (FlatAffineCompleteVertices.vertexEquiv (inputs true P depth old level) (cone true P depth old level) u
        ⟨midpointWord P depth old level (LeanCanny.pair u w), midpointWord_valid P depth old level u w hw hs⟩) =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
          (originalParent P depth old level u (memberRoot P depth old level false u w hw)) ∧
        2 * y (coordinateFin P depth old u) =
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ (memberRoot P depth old level false u w hw).val +
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ (memberRoot P depth old level true u w hw).val} :=
  (congrArg (FlatAffineCompleteComponentSamples.slice (inputs true P depth old level) u)
    (midpointWord_root P depth old level u w hw hs)).trans (midpoint_slice P depth old level u w hn hw hs)

theorem exists_midpointWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x y : FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u)
    (hshared : originalParent P depth old level u x = originalParent P depth old level u y) :
    ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
      (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level),
      FlatAffineCompleteVertices.vertexEquiv (inputs true P depth old level) (cone true P depth old level) u
        ⟨midpointWord P depth old level (LeanCanny.pair u w), midpointWord_valid P depth old level u w hw hs⟩ =
          CoordinateDoubleAffineChildRecords.midpointRoot P depth old level u x y hshared := by
  obtain ⟨w, hw, hs, hx, hy⟩ := exists_shared_original_pair P depth old level u x y hshared
  refine ⟨w, hw, hs, ?_⟩
  have H := midpointWord_root P depth old level u w hw hs
  unfold midpointRoot at H
  subst x
  subst y
  exact H

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
