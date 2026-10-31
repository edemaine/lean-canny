/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSharedCriticalPairs
public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointGeometry

/-! # Validated shared-parent words construct actual midpoint child roots

The native pair validator supplies the exact shared-ancestry identity needed
by the midpoint root constructor. The resulting slice uses the two original
critical coordinates and the original parent, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra
open CoordinateDoubleAffineChildRecords (originalParent retainedCoordinate coordinateFin)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberRoot memberWord parentWord SquareSampleCompleteVertices.Valid

theorem shared_originals (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    originalParent P depth old level u (memberRoot P depth old level false u w hw) =
      originalParent P depth old level u (memberRoot P depth old level true u w hw) :=
  (shared_packet P depth old level u w hw).mp hs

noncomputable def midpointRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffineChildRecords.inputs true P depth old level) u :=
  CoordinateDoubleAffineChildRecords.midpointRoot P depth old level u
    (memberRoot P depth old level false u w hw) (memberRoot P depth old level true u w hw)
    (shared_originals P depth old level u w hw hs)

theorem midpoint_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffineChildRecords.inputs true P depth old level) u
        (midpointRoot P depth old level u w hw hs) =
      {y | y ∈ FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u
          (originalParent P depth old level u (memberRoot P depth old level false u w hw)) ∧
        2 * y (coordinateFin P depth old u) =
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ (memberRoot P depth old level false u w hw).val +
          retainedCoordinate P depth old u (depth u + 1) ⟨depth u, by omega⟩ (memberRoot P depth old level true u w hw).val} :=
  CoordinateDoubleAffineChildRecords.midpointRoot_slice P depth old level u hn
    (memberRoot P depth old level false u w hw) (memberRoot P depth old level true u w hw)
    (shared_originals P depth old level u w hw hs)

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
