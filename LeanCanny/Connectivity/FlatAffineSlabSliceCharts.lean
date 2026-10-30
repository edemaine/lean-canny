/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabParentSections
public import LeanCanny.Encoding.FlatAffineSliceConstraintMap

/-! # Constructed interval charts for the actual coarser affine slice -/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabSliceCharts
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue)
open FlatAffineSlabGraphBranches (Family)
open FlatAffineShiftedSlice (coarseSlice projection)
open FlatAffineSliceConstraintMap (map target active)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def domainHomeomorph (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (h : Fin (arity F u)) (hs : h ∈ active F u)
    (a b : ℝ) : (projection F u x h) ⁻¹' Ioo a b ≃ₜ
      (ConstraintLineCharts.projection (map F u) (target F u x) (some ⟨h, hs⟩)) ⁻¹' Ioo a b where
  toFun y := ⟨⟨y.val.val, (FlatAffineSliceConstraintMap.coarse_iff F u x h hs y.val.val).mpr y.val.property⟩, by
    change map F u y.val.val (some ⟨h, hs⟩) - target F u x (some ⟨h, hs⟩) ∈ Ioo a b
    rw [FlatAffineSliceConstraintMap.height_eq]
    exact y.property⟩
  invFun y := ⟨⟨y.val.val, (FlatAffineSliceConstraintMap.coarse_iff F u x h hs y.val.val).mp y.val.property⟩, by
    change FlatAffineShiftedSlice.heightValue F u x h y.val.val ∈ Ioo a b
    rw [← FlatAffineSliceConstraintMap.height_eq F u x h hs]
    exact y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem exists_charts (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      FermatCoordinateCone.normal j i)
    (hactive : h ∈ active F (original c))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) :
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
    have HS := B.shifted_slice_regular F cone height c hc h hheight hnormal hactive x t y HF
    exact (FlatAffineSliceConstraintMap.map_derivative F u y).symm ▸ HS
  obtain ⟨C, HC, HF⟩ := ConstraintLineCharts.exists_charts (map F u) (target F u x) r a b
    (fun y _ => (FlatAffineSliceConstraintMap.contDiff_map F u).contDiffAt.of_le le_top) HR
  let e := domainHomeomorph F u x h hactive a b
  let chart (y : (projection F u x h) ⁻¹' Ioo a b) := e.toOpenPartialHomeomorph.trans (C (e y))
  refine ⟨chart, ?_, ?_⟩
  · intro y
    exact ⟨mem_univ y, HC (e y)⟩
  · intro z y hy
    have HE := HF (e z) (e y) hy.2
    apply Subtype.ext
    exact (congrArg Subtype.val HE).trans (FlatAffineSliceConstraintMap.height_eq F u x h hactive y.val.val)

end LeanCanny.Connectivity.FlatAffineSlabSliceCharts
