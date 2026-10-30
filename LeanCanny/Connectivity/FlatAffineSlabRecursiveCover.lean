/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabSaturation

/-! # Recursive endpoint covers attach the actual original component slab

The interior saturation is constructed from the original records. Clopen
path covers of its two endpoint fibers then produce a finite clopen path
cover of the actual closed slab. Selected endpoint attachments retain an
additive sum of the branch and endpoint label types.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabRecursiveCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineShiftedSlice (projection)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem exists_component_cover {L R : Type*} [Finite L] [Finite R] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      FermatCoordinateCone.normal j i)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (hobjective : ¬∃ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
          d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (left : ClopenPathCover ((projection F (original c) x h) ⁻¹' {endpointValue (next F) cone height false c}) L)
    (right : ClopenPathCover ((projection F (original c) x h) ⁻¹' {endpointValue (next F) cone height true c}) R) :
    Nonempty (ClopenPathCover ((projection F (original c) x h) ⁻¹' Icc
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
      (ComponentSlabCover.SelectedIndex (ParentIndex F cone height c x) L R)) := by
  let : Finite (ParentIndex F cone height c x) := FlatAffineSlabGraphBranches.parentIndex_finite F cone height c hc x
  obtain ⟨D, _, _, _⟩ := FlatAffineSlabSaturation.exists_interior_data F cone height c B hc h hheight hnormal hactive hobjective x
  obtain ⟨l, r, HS⟩ := ComponentSlabCover.exists_selection D left right
  have HP := (FlatAffineShiftedSlice.projection_proper F (original c) x h).continuous
  have HAB := FlatAffineSlabGraphContext.endpoints_lt (next F) cone height c hc
  let t0 : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) :=
    ⟨sampleValue (next F) cone height false c, FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc⟩
  exact ⟨ClopenPathCover.ofClosed (ComponentSlabCover.selectedPiece D left right l r)
    (ComponentSlabCover.selected_closed D left right l r HP)
    (ComponentSlabCover.selected_cover D left right l r HS)
    (ComponentSlabCover.selected_paths D left right l r HP HAB t0)⟩

end LeanCanny.Connectivity.FlatAffineSlabRecursiveCover
