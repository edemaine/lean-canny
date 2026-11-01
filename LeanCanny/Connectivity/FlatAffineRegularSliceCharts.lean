/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineSlabSliceCharts
public import LeanCanny.Connectivity.FlatAffineSlabRegularSampling
/-! # Actual regular slice charts do not require an absolute branch family -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineRegularSliceCharts
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineSliceConstraintMap (map target active)
open FlatAffineShiftedSlice (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_charts (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hh : h ∈ active F u) (A B : ℝ)
    (HR : FlatAffineSlabRegularData.RegularOn F u x h A B) :
    ∃ chart : ∀ y : (projection F u x h) ⁻¹' Ioo A B,
      OpenPartialHomeomorph ((projection F u x h) ⁻¹' Ioo A B)
        (Ioo A B × (fderiv ℝ (map F u) y.val.val).ker),
      (∀ y, y ∈ (chart y).source) ∧
      ∀ z y, y ∈ (chart z).source → (chart z y).1 = (Ioo A B).restrictPreimage (projection F u x h) y := by
  let r : Option (active F u) := some ⟨h,hh⟩
  have HD (y : Fin (arity F u) → ℝ)
      (hy : map F u y ∈ CoordinateLineInterval.region (target F u x) r A B) :
      Function.Surjective (fderiv ℝ (map F u) y) := by
    have HY := (FlatAffineSliceConstraintMap.coarse_iff F u x h hh y).mp hy.1
    let t : Ioo A B := ⟨FlatAffineShiftedSlice.heightValue F u x h y, by
      rw [← FlatAffineSliceConstraintMap.height_eq F u x h hh]
      exact hy.2⟩
    have HF : y ∈ FlatAffineShiftedSlice.slice F u x h t.val :=
      (FlatAffineShiftedSlice.slice_iff_fiber F u x h hh t.val y).mpr ⟨HY,rfl⟩
    exact (FlatAffineSliceConstraintMap.map_derivative F u y).symm ▸ HR t y HF
  obtain ⟨C,HC,HF⟩ := ConstraintLineCharts.exists_charts (map F u) (target F u x) r A B
    (fun y _ => (FlatAffineSliceConstraintMap.contDiff_map F u).contDiffAt.of_le le_top) HD
  let e := FlatAffineSlabSliceCharts.domainHomeomorph F u x h hh A B
  let chart (y : (projection F u x h) ⁻¹' Ioo A B) := e.toOpenPartialHomeomorph.trans (C (e y))
  refine ⟨chart,fun y => ⟨mem_univ y,HC (e y)⟩,?_⟩
  intro z y hy
  have HE := HF (e z) (e y) hy.2
  apply Subtype.ext
  exact (congrArg Subtype.val HE).trans (FlatAffineSliceConstraintMap.height_eq F u x h hh y.val.val)

end LeanCanny.Connectivity.FlatAffineRegularSliceCharts
