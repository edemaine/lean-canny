/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSliceRegularity
public import LeanCanny.Encoding.CoordinateAffineSliceControls

/-! # Native regularity decisions for generated coordinate-prefix slices

The next-stage cone and independent normals come from the actual coordinate
records. Native polynomial-space search therefore decides singularity and
regularity of the entire frozen slice, without a supplied regularity oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffineSliceRegularity
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open CoordinateAffinePrefix (inputs)
open FlatAffineCompleteRootStages (next)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem cone (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) :
    FlatAffinePowerPositive.ConeCertificate (next (inputs P depth objective level)) :=
  CoordinateAffinePrefix.coneCertificate P (fun u => depth u + 1) objective level

theorem singular_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    FlatAffineSliceRegularity.singularLanguage (inputs P depth objective level) (cone P depth objective level) ∈ PSPACE :=
  FlatAffineSliceRegularity.singular_mem_PSPACE (CoordinateAffinePrefix.access hP hd ho hl hA) (cone P depth objective level)

theorem regular_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    FlatAffineSliceRegularity.regularLanguage (inputs P depth objective level) (cone P depth objective level) ∈ PSPACE :=
  FlatAffineSliceRegularity.regular_mem_PSPACE (CoordinateAffinePrefix.access hP hd ho hl hA) (cone P depth objective level)

theorem singular_correct (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v : List Bool)
    (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (parentCone (inputs P depth objective level) (cone P depth objective level)) u v) :
    pair u v ∈ FlatAffineSliceRegularity.singularLanguage (inputs P depth objective level) (cone P depth objective level) ↔
      (FlatAffineSingularSliceSamples.singular (inputs P depth objective level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
          (parentCone (inputs P depth objective level) (cone P depth objective level)) u ⟨v, hv⟩)).Nonempty :=
  FlatAffineSliceRegularity.singular_correct (inputs P depth objective level) (cone P depth objective level) u v hv
    (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))

theorem regular_correct (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v : List Bool)
    (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level)
      (parentCone (inputs P depth objective level) (cone P depth objective level)) u v) :
    pair u v ∈ FlatAffineSliceRegularity.regularLanguage (inputs P depth objective level) (cone P depth objective level) ↔
      ∀ z ∈ FlatAffineCompleteComponentSamples.slice (inputs P depth objective level) u
        (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level)
          (parentCone (inputs P depth objective level) (cone P depth objective level)) u ⟨v, hv⟩),
        Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
          (FlatAffineCompleteComponentSamples.source (inputs P depth objective level) u)
          (FlatAffineCompleteComponentSamples.active (inputs P depth objective level) u)
          (FlatAffineCompleteComponentSamples.direction (inputs P depth objective level) u) z) :=
  FlatAffineSliceRegularity.regular_correct (inputs P depth objective level) (cone P depth objective level) u v hv
    (CoordinateAffineSliceControls.normals_independent P depth objective level u (depth u))

end LeanCanny.Encoding.CoordinateAffineSliceRegularity
