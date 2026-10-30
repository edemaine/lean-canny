/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabParentBranches
public import LeanCanny.Encoding.FlatAffineShiftedSliceProjection

/-! # Actual continuous sections of the coarser slice's height projection

The parent-filtered critical branches become continuous sections in the
original compact coarser slice. Each has a continuous extension through both
closed-slab endpoints, where slice regularity is not assumed.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabParentSections
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open FlatAffineSlabGraphBranches (Family ParentIndex)
open FlatAffineShiftedSlice (coarseSlice projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

section
variable (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
  (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
  (c : List Bool) (B : Family (next F) cone height c)
  (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
  (h : Fin (arity F (original c)))
  (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
  (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
  (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))

include B hc hheight hactive

theorem feasible (j : ParentIndex F cone height c x)
    (r : Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r.val) ∈ coarseSlice F (original c) x h ∧
      FlatAffineShiftedSlice.heightValue F (original c) x h
        (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r.val)) = r.val :=
  (FlatAffineShiftedSlice.slice_iff_fiber F (original c) x h hactive r.val _).mp
    (B.parent_spatial_mem F cone height c hc h hheight hactive x j r)

noncomputable def arc (j : ParentIndex F cone height c x) (r : ℝ) : coarseSlice F (original c) x h :=
  if hr : r ∈ Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) then
    ⟨FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r),
      (feasible F cone height c B hc h hheight hactive x j ⟨r, hr⟩).1⟩
  else
    ⟨FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val (sampleValue (next F) cone height false c)),
      (feasible F cone height c B hc h hheight hactive x j
        ⟨_, Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc)⟩).1⟩

theorem arc_value (j : ParentIndex F cone height c x) (r : ℝ)
    (hr : r ∈ Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    (arc F cone height c B hc h hheight hactive x j r).val =
      FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r) := by
  simp only [arc, dite_eq_left hr]

theorem arc_level (j : ParentIndex F cone height c x) (r : ℝ)
    (hr : r ∈ Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    projection F (original c) x h (arc F cone height c B hc h hheight hactive x j r) = r := by
  exact (congrArg (FlatAffineShiftedSlice.heightValue F (original c) x h)
    (arc_value F cone height c B hc h hheight hactive x j r hr)).trans
      (feasible F cone height c B hc h hheight hactive x j ⟨r, hr⟩).2

theorem arc_continuous (j : ParentIndex F cone height c x) :
    ContinuousOn (arc F cone height c B hc h hheight hactive x j)
      (Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have HC := continuousOn_iff_continuous_domRestrict.mp (B.parent_spatial_continuous F cone height c x j)
  have HD : Continuous (fun r : Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c) =>
      (⟨FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r.val),
        (feasible F cone height c B hc h hheight hactive x j r).1⟩ : coarseSlice F (original c) x h)) := HC.subtype_mk _
  apply HD.congr
  intro r
  exact Subtype.ext (arc_value F cone height c B hc h hheight hactive x j r.val r.property).symm

noncomputable def sections (j : ParentIndex F cone height c x) :
    C(Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c),
      (projection F (original c) x h) ⁻¹' Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) := by
  let S := Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)
  let f (r : S) := arc F cone height c B hc h hheight hactive x j r.val
  have HF : Continuous f := continuousOn_iff_continuous_domRestrict.mp
    ((arc_continuous F cone height c B hc h hheight hactive x j).mono Ioo_subset_Icc_self)
  have HM (r : S) : projection F (original c) x h (f r) ∈ S :=
    (arc_level F cone height c B hc h hheight hactive x j r.val (Ioo_subset_Icc_self r.property)).symm ▸ r.property
  exact ⟨fun r => ⟨f r, HM r⟩, HF.subtype_mk HM⟩

theorem sections_project (j : ParentIndex F cone height c x)
    (r : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    (Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)).restrictPreimage
      (projection F (original c) x h) (sections F cone height c B hc h hheight hactive x j r) = r :=
  Subtype.ext (arc_level F cone height c B hc h hheight hactive x j r.val (Ioo_subset_Icc_self r.property))

theorem sections_cover_fibers
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      FermatCoordinateCone.normal j i)
    (hobjective : ¬∃ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
          d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ))
    (y : (projection F (original c) x h) ⁻¹' Ioo
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    ∃ j : ParentIndex F cone height c x,
      JoinedIn (((Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)).restrictPreimage
        (projection F (original c) x h)) ⁻¹' {
          (Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)).restrictPreimage
            (projection F (original c) x h) y}) y
        (sections F cone height c B hc h hheight hactive x j
          ((Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)).restrictPreimage
            (projection F (original c) x h) y)) := by
  let p := projection F (original c) x h
  let S := Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)
  let t : S := S.restrictPreimage p y
  have HY : y.val.val ∈ FlatAffineShiftedSlice.slice F (original c) x h t.val :=
    (FlatAffineShiftedSlice.slice_iff_fiber F (original c) x h hactive t.val y.val.val).mpr ⟨y.val.property, rfl⟩
  obtain ⟨j, HJ⟩ := B.sample_parent_branch F cone height c hc h hheight hnormal hactive hobjective x t y.val.val HY
  refine ⟨j, ?_⟩
  apply (RegularComponentTransport.joinedIn_restrictPreimage_iff p S t y
    (sections F cone height c B hc h hheight hactive x j t) rfl
      (sections_project F cone height c B hc h hheight hactive x j t)).mpr
  apply (FlatAffineShiftedSlice.joined_fiber_iff F (original c) x h hactive t.val y.val
    (sections F cone height c B hc h hheight hactive x j t).val rfl
      (arc_level F cone height c B hc h hheight hactive x j t.val (Ioo_subset_Icc_self t.property))).mpr
  have HE := arc_value F cone height c B hc h hheight hactive x j t.val (Ioo_subset_Icc_self t.property)
  exact HE.symm ▸ HJ

end
end LeanCanny.Connectivity.FlatAffineSlabParentSections
