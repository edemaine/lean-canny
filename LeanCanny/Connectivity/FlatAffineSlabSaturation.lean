/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabSliceCharts
public import LeanCanny.Connectivity.FiberSectionLimit
public import LeanCanny.Connectivity.ComponentSlabCover

/-! # Saturated original components from the actual parent critical branches

All local charts, sections, properness, and fiber-component sampling are
constructed from the original source. Saturation therefore covers every
point of the original open slab. Its pieces are clopen and path connected,
have connected limits at both endpoints, and overlap exactly when their
critical samples are connected in the retained sample fiber.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabSaturation
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
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      FermatCoordinateCone.normal j i)
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
  let u := original c
  let a := endpointValue (next F) cone height false c
  let b := endpointValue (next F) cone height true c
  let S := Ioo a b
  let p := projection F u x h
  let t0 : S := ⟨sampleValue (next F) cone height false c, FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc⟩
  let : ContractibleSpace S := (convex_Ioo a b).contractibleSpace ⟨t0.val, t0.property⟩
  let sections := FlatAffineSlabParentSections.sections F cone height c B hc h hheight hactive x
  let arc := FlatAffineSlabParentSections.arc F cone height c B hc h hheight hactive x
  have HP := FlatAffineShiftedSlice.projection_proper F u x h
  have HAB : a < b := FlatAffineSlabGraphContext.endpoints_lt (next F) cone height c hc
  have Hproj := FlatAffineSlabParentSections.sections_project F cone height c B hc h hheight hactive x
  have Hcover := FlatAffineSlabParentSections.sections_cover_fibers F cone height c B hc h hheight hactive x hnormal hobjective
  obtain ⟨C, HC, HF⟩ := FlatAffineSlabSliceCharts.exists_charts F cone height c B hc h hheight hnormal hactive x
  let piece := FiberSectionCover.piece (S.restrictPreimage p) sections
  have Hcl (j : ParentIndex F cone height c x) : IsClopen (piece j) :=
    FiberSectionCover.isClopen_piece (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj j
  have HA := FlatAffineSlabParentSections.arc_continuous F cone height c B hc h hheight hactive x
  have HL := FlatAffineSlabParentSections.arc_level F cone height c B hc h hheight hactive x
  let D : ComponentSlabCover.InteriorData p a b (ParentIndex F cone height c x) := {
    piece := piece
    closed j := (Hcl j).isClosed
    cover := FiberSectionCover.cover (S.restrictPreimage p) sections Hcover
    paths := FiberSectionCover.paths (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj
    arc := arc
    continuous_arc := HA
    arc_mem j t := ⟨sections j t, FiberSectionCover.section_mem_piece (S.restrictPreimage p) sections Hproj j t, rfl⟩
    level_left j := HL j a ⟨le_rfl, HAB.le⟩
    level_right j := HL j b ⟨HAB.le, le_rfl⟩
    limit_left j := (FiberSectionCover.isConnected_ambient_endpoint p sections C HC HF HP Hproj HAB j).isPreconnected
    limit_right j := (FiberSectionCover.isConnected_ambient_endpoint_right p sections C HC HF HP Hproj HAB j).isPreconnected }
  refine ⟨D, Hcl, FlatAffineSlabParentSections.arc_value F cone height c B hc h hheight hactive x, ?_⟩
  intro i j
  have HE := FiberSectionCover.overlap_iff_sample (S.restrictPreimage p) sections C HC HF (HP.restrictPreimage S) Hproj t0 i j
  have HJ := RegularComponentTransport.joinedIn_restrictPreimage_iff p S t0 (sections i t0) (sections j t0) (Hproj i t0) (Hproj j t0)
  have HK := FlatAffineShiftedSlice.joined_fiber_iff F u x h hactive t0.val (sections i t0).val (sections j t0).val
    (HL i t0.val (Ioo_subset_Icc_self t0.property)) (HL j t0.val (Ioo_subset_Icc_self t0.property))
  have Hi : (sections i t0).val.val = FlatAffineShiftedSlice.spatialPoint F u (B.curve i.val t0.val) :=
    FlatAffineSlabParentSections.arc_value F cone height c B hc h hheight hactive x i t0.val (Ioo_subset_Icc_self t0.property)
  have Hj : (sections j t0).val.val = FlatAffineShiftedSlice.spatialPoint F u (B.curve j.val t0.val) :=
    FlatAffineSlabParentSections.arc_value F cone height c B hc h hheight hactive x j t0.val (Ioo_subset_Icc_self t0.property)
  simpa only [Hi, Hj] using HE.trans (HJ.trans HK)

end LeanCanny.Connectivity.FlatAffineSlabSaturation
