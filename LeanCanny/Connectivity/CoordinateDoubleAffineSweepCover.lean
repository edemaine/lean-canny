/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSweepOriginalSamples
public import LeanCanny.Encoding.CoordinateDoubleAffineSweepRows
public import LeanCanny.Connectivity.FlatAffineScaledSlabRecursiveCover

/-! # Recursive slab attachment for the actual next coordinate sweep

The original records compute the sweep coordinate, height row, cone
certificate, normals, and objective. The frozen parent is transported without
changing its tuple. Endpoint covers remain the lower-dimensional recursive
obligations; attaching them constructs the actual closed-slab component cover.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineSweepCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineShiftedSlice (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (level : List Bool → List Bool)
local notation "G" => CoordinateDoubleAffineSweep.inputs P depth old level
local notation "C" => CoordinateDoubleAffineSweep.cone P depth old level
local notation "H" => CoordinateDoubleAffineSweep.height P depth old level
local notation "r" => CoordinateDoubleAffineSweep.coordinate P depth old

theorem exists_component_cover {L R : Type*} [Finite L] [Finite R]
    (c : List Bool) (B : Family (next G) C H c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next G) C H)
    (hn : old (FlatAffineFullSourceTower.stage (original c) (depth (original c))) < P.dim (original c) + 3)
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) (original c))
    (left : ClopenPathCover ((projection G (original c) (CoordinateDoubleAffineSweep.parent P depth old level (original c) x) (r (original c))) ⁻¹'
      {endpointValue (next G) C H false c}) L)
    (right : ClopenPathCover ((projection G (original c) (CoordinateDoubleAffineSweep.parent P depth old level (original c) x) (r (original c))) ⁻¹'
      {endpointValue (next G) C H true c}) R) :
    Nonempty (ClopenPathCover ((projection G (original c) (CoordinateDoubleAffineSweep.parent P depth old level (original c) x) (r (original c))) ⁻¹'
      Icc (endpointValue (next G) C H false c) (endpointValue (next G) C H true c))
      (ComponentSlabCover.SelectedIndex
        (ParentIndex G C H c (CoordinateDoubleAffineSweep.parent P depth old level (original c) x)) L R)) := by
  exact FlatAffineScaledSlabRecursiveCover.exists_component_cover G C H c B hc (r (original c)) rfl
    (fun _ => 2) (fun _ => by decide)
    (CoordinateDoubleAffinePrefix.normal P depth (CoordinateDoubleAffineSweep.objective depth old) level _ _)
    (CoordinateDoubleAffineSweep.sweep_active P depth old level (original c) hn)
    (CoordinateDoubleAffineSliceControls.objective_independent P depth (CoordinateDoubleAffineSweep.objective depth old) level _ _)
    (CoordinateDoubleAffineSweep.parent P depth old level (original c) x) left right

end LeanCanny.Connectivity.CoordinateDoubleAffineSweepCover
