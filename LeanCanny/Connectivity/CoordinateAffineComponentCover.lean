/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineCompactComponentCover
public import LeanCanny.Encoding.CoordinateAffineSliceControls
public import LeanCanny.Encoding.FlatAffineSliceCompact

/-! # Constructed component covers for actual coordinate-prefix slices

The source gives compactness; generated coordinate records give independent
normals and cone certificates. Every actual parent therefore has a finite
clopen connected cover indexed by native complete children, including singular
slice components, without a supplied geometric cover or regularity promise.
The remaining sample connection tests are the recursive obligation.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateAffineComponentCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineCompleteRootStages (next)
open FlatAffineCompleteComponentSamples (slice)
open CoordinateAffinePrefix (inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem cone (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) :
    FlatAffinePowerPositive.ConeCertificate (next (inputs P depth objective level)) :=
  CoordinateAffinePrefix.coneCertificate P (fun u => depth u + 1) objective level

theorem finite_components (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (inputs P depth objective level) u) :
    Finite (ConnectedComponents (slice (inputs P depth objective level) u x)) ∧
      Nat.card (ConnectedComponents (slice (inputs P depth objective level) u x)) ≤
        FlatAffinePowerSampleInput.originalCountBound (next (inputs P depth objective level)) u :=
  FlatAffineCompactComponentSamples.finite_card_le (inputs P depth objective level) (cone P depth objective level) u x
    (FlatAffineSliceCompact.compact _ u x)
    (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))
    (CoordinateAffineSliceControls.objective_independent P depth objective level u (depth u))

section Cover
variable (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
  (level : List Bool → List Bool) (u v : List Bool)
  (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
    (FlatAffineCompleteChildLabels.parentCone (inputs P depth objective level) (cone P depth objective level)) u v)

theorem piece_isClopen (w : List Bool) :
    IsClopen (FlatAffineCompactComponentCover.piece (inputs P depth objective level) (cone P depth objective level) u v hv w) :=
  FlatAffineCompactComponentCover.piece_isClopen (inputs P depth objective level) (cone P depth objective level) u v hv
    (FlatAffineSliceCompact.compact _ u _) (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))
    (CoordinateAffineSliceControls.objective_independent P depth objective level u (depth u)) w

theorem cover (z : FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (cone P depth objective level) u v hv) :
    ∃ w, FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (cone P depth objective level) u v w ∧
      z ∈ FlatAffineCompactComponentCover.piece (inputs P depth objective level) (cone P depth objective level) u v hv w :=
  FlatAffineCompactComponentCover.cover (inputs P depth objective level) (cone P depth objective level) u v hv
    (FlatAffineSliceCompact.compact _ u _) (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))
    (CoordinateAffineSliceControls.objective_independent P depth objective level u (depth u)) z

theorem connected_iff_sample_connections :
    IsPreconnected (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (cone P depth objective level) u v hv) ↔
      ∀ (w z : List Bool)
        (hw : FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (cone P depth objective level) u v w)
        (hz : FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (cone P depth objective level) u v z),
        (FlatAffineCompactComponentCover.point (inputs P depth objective level) (cone P depth objective level) u v hv z hz).val ∈
          connectedComponentIn (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (cone P depth objective level) u v hv)
            (FlatAffineCompactComponentCover.point (inputs P depth objective level) (cone P depth objective level) u v hv w hw).val :=
  FlatAffineCompactComponentCover.connected_iff_sample_connections (inputs P depth objective level) (cone P depth objective level) u v hv
    (FlatAffineSliceCompact.compact _ u _) (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))
    (CoordinateAffineSliceControls.objective_independent P depth objective level u (depth u))

theorem valid_mem_PSPACE (hP : P.PolyTime) (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    FlatAffineCompleteChildLabels.language (inputs P depth objective level) (cone P depth objective level) ∈ PSPACE :=
  FlatAffineCompleteChildLabels.mem_PSPACE (CoordinateAffinePrefix.access hP hd ho hl hA) (cone P depth objective level)

theorem width_unary (hP : P.PolyTime) (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    UnaryFn (FlatAffineCompleteVertices.width (next (inputs P depth objective level)) (cone P depth objective level)) :=
  FlatAffineCompleteVertices.width_unary
    (FlatAffineCompleteChildLabels.nextAccess (CoordinateAffinePrefix.access hP hd ho hl hA)) (cone P depth objective level)

end Cover
end LeanCanny.Connectivity.CoordinateAffineComponentCover
