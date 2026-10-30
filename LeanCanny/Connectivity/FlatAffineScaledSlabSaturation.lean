/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabRegularSaturation
public import LeanCanny.Connectivity.FlatAffineScaledSlabSliceRegularity

/-! # Saturated original slabs for independently scaled coordinate normals

The source certificate and retained branch family prove regularity of every
interior fiber. The constructed saturation covers all original points and
retains exact branch arcs and sample-fiber overlap semantics.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineScaledSlabSaturation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineShiftedSlice (projection)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem exists_interior_data (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (scale : Fin (arity F (original c)) → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      scale j * FermatCoordinateCone.normal j i)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (hobjective : ¬∃ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
          d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) :
    ∃ D : ComponentSlabCover.InteriorData (projection F (original c) x h)
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) (ParentIndex F cone height c x),
      (∀ j, IsClopen (D.piece j)) ∧
      (∀ j r, r ∈ Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) →
        (D.arc j r).val = FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r)) ∧
      ∀ i j, ClosedPathCover.Overlap D.piece i j ↔
        JoinedIn (FlatAffineShiftedSlice.slice F (original c) x h (sampleValue (next F) cone height false c))
          (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve i.val (sampleValue (next F) cone height false c)))
          (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val (sampleValue (next F) cone height false c))) := by
  have HR : FlatAffineSlabRegularData.RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) :=
    fun t y hy => B.shifted_slice_regular_scaled F cone height c hc h hheight scale hscale hnormal hactive x t y hy
  exact FlatAffineSlabRegularData.exists_interior_data F cone height c B hc h hheight hactive hobjective x HR

end LeanCanny.Connectivity.FlatAffineScaledSlabSaturation
