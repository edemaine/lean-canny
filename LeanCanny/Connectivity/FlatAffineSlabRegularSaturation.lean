/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabRegularSampling
public import LeanCanny.Connectivity.FlatAffineSlabSaturation

/-! # Original component saturation from proved fiber regularity

Coordinate source certificates provide the regularity proof. All remaining
charts, properness, sections, coverage, and connected endpoint limits are
constructed for the actual compact coarser slice.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabRegularData
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineShiftedSlice (projection)
open FlatAffineSliceConstraintMap (map target active)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem exists_charts (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (_B : Family (next F) cone height c)
    (_hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (_hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ active F (original c))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (hregular : RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    ∃ chart : ∀ y : (projection F (original c) x h) ⁻¹' Ioo
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c),
      OpenPartialHomeomorph ((projection F (original c) x h) ⁻¹' Ioo
        (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
        (Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) ×
          (fderiv ℝ (map F (original c)) y.val.val).ker),
      (∀ y, y ∈ (chart y).source) ∧
      ∀ z y, y ∈ (chart z).source → (chart z y).1 =
        (Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)).restrictPreimage
          (projection F (original c) x h) y := by
  let u := original c
  let a := endpointValue (next F) cone height false c
  let b := endpointValue (next F) cone height true c
  let r : Option (active F u) := some ⟨h, hactive⟩
  have HR (y : Fin (arity F u) → ℝ)
      (hy : map F u y ∈ CoordinateLineInterval.region (target F u x) r a b) :
      Function.Surjective (fderiv ℝ (map F u) y) := by
    have HY := (FlatAffineSliceConstraintMap.coarse_iff F u x h hactive y).mp hy.1
    let t : Ioo a b := ⟨FlatAffineShiftedSlice.heightValue F u x h y, by
      rw [← FlatAffineSliceConstraintMap.height_eq F u x h hactive]
      exact hy.2⟩
    have HF : y ∈ FlatAffineShiftedSlice.slice F u x h t.val :=
      (FlatAffineShiftedSlice.slice_iff_fiber F u x h hactive t.val y).mpr ⟨HY, rfl⟩
    have HS := hregular t y HF
    exact (FlatAffineSliceConstraintMap.map_derivative F u y).symm ▸ HS
  obtain ⟨C, HC, HF⟩ := ConstraintLineCharts.exists_charts (map F u) (target F u x) r a b
    (fun y _ => (FlatAffineSliceConstraintMap.contDiff_map F u).contDiffAt.of_le le_top) HR
  let e := FlatAffineSlabSliceCharts.domainHomeomorph F u x h hactive a b
  let chart (y : (projection F u x h) ⁻¹' Ioo a b) := e.toOpenPartialHomeomorph.trans (C (e y))
  refine ⟨chart, ?_, ?_⟩
  · intro y
    exact ⟨mem_univ y, HC (e y)⟩
  · intro z y hy
    have HE := HF (e z) (e y) hy.2
    apply Subtype.ext
    exact (congrArg Subtype.val HE).trans (FlatAffineSliceConstraintMap.height_eq F u x h hactive y.val.val)


theorem exists_interior_data (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (hobjective : ¬∃ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
          d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (hregular : RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
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
  have Hcover := FlatAffineSlabRegularData.cover_fibers F cone height c B hc h hheight hactive hobjective x hregular
  obtain ⟨C, HC, HF⟩ := FlatAffineSlabRegularData.exists_charts F cone height c B hc h hheight hactive x hregular
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


end LeanCanny.Connectivity.FlatAffineSlabRegularData
