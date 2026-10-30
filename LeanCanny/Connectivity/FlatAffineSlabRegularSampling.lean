/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabParentSections

/-! # Fiber sampling from proved regularity of the actual original slices

The regularity statement is proof data. Coordinate and scaled-coordinate
records construct it from their native cone certificates. All compactness,
critical-root lifts, branch filtering, and sections remain constructed here.
-/

@[expose] public section
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Connectivity
open LeanCanny.Encoding.FlatAffineFullSourceTower (Inputs arity stageWidth)
open LeanCanny.Encoding.FlatAffineCompleteRootStages (next)
open LeanCanny.Connectivity.FlatAffineSlabGraphArcs (original Index equation)
open LeanCanny.Encoding.FlatAffineSlabGraphContext (endpointValue sampleValue)
open LeanCanny.Connectivity.FlatAffineSlabGraphBranches (Family ParentIndex)
open LeanCanny.Encoding.FlatAffineShiftedSlice (projection)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace LeanCanny.Connectivity.FlatAffineSlabRegularData

def RegularOn (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (a b : ℝ) : Prop :=
  ∀ t : Ioo a b, ∀ y ∈ FlatAffineShiftedSlice.slice F u x h t.val,
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineFullSourceTower.free F u (F.depth u))
      (FlatAffineFullSourceTower.direction F u (F.depth u)) y)

end LeanCanny.Connectivity.FlatAffineSlabRegularData

namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches

theorem Family.sample_shifted_slice_of_regular (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (_hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (hobjective : ¬∃ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      ∀ i, (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) 0 i : ℝ) =
        ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
          d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (hregular : FlatAffineSlabRegularData.RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (t : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (y : Fin (arity F (original c)) → ℝ) (hy : y ∈ FlatAffineShiftedSlice.slice F (original c) x h t.val) :
    ∃ j : Index (next F) cone height c,
      FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j t.val) = x.val ∧
      JoinedIn (FlatAffineShiftedSlice.slice F (original c) x h t.val) y
        (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j t.val)) := by
  obtain ⟨z, mu, _, HJ, HR⟩ := FlatAffineShiftedComponentSampling.exists_joined_stage_root (Int.castRingHom ℝ)
    (BoundedFullCriticalSamples.polynomial F.source (original c))
    (FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)))
    (fun i => (FlatAffineFullSourceTower.level F (original c) (F.depth (original c)) i).polynomial)
    (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F (original c)) (F.depth (original c))) h hactive t.val
    (FlatAffineShiftedSlice.compact F (original c) x h t.val)
    (fun z hz => hregular t z hz)
    hobjective y hy
  obtain ⟨q, HQ, HA, HS⟩ := FlatAffineShiftedSlice.exists_power_lift F (original c) x h hactive t.val z mu HR
  have HE : equation (next F) height c t.val q := by
    change ∀ i, (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ) q =
      if i = height (original c) then t.val else 0
    simpa only [hheight] using HQ
  obtain ⟨j, HC, _⟩ := (B.complete t q).mp HE
  refine ⟨j, (congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) HC).trans HA, ?_⟩
  have HP := (congrArg (FlatAffineShiftedSlice.spatialPoint F (original c)) HC).trans HS
  exact HP.symm ▸ HJ


theorem Family.sample_parent_branch_of_regular (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
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
    (hregular : FlatAffineSlabRegularData.RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (t : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (y : Fin (arity F (original c)) → ℝ) (hy : y ∈ FlatAffineShiftedSlice.slice F (original c) x h t.val) :
    ∃ j : ParentIndex F cone height c x,
      JoinedIn (FlatAffineShiftedSlice.slice F (original c) x h t.val) y
        (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val t.val)) := by
  obtain ⟨j, HA, HJ⟩ := B.sample_shifted_slice_of_regular F cone height c hc h hheight hactive hobjective x hregular t y hy
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc)
  have HE := B.original_ancestor_constant F cone height c h hheight hactive j
    ⟨t.val, Ioo_subset_Icc_self t.property⟩ ⟨_, HT⟩
  have HP := HE.trans (congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) (B.anchor j))
  exact ⟨⟨j, HP.symm.trans HA⟩, HJ⟩


end LeanCanny.Connectivity.FlatAffineSlabGraphBranches

namespace LeanCanny.Connectivity.FlatAffineSlabRegularData
open FlatAffineSlabParentSections

theorem cover_fibers (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
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
    (hregular : FlatAffineSlabRegularData.RegularOn F (original c) x h
      (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
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
  obtain ⟨j, HJ⟩ := B.sample_parent_branch_of_regular F cone height c hc h hheight hactive hobjective x hregular t y.val.val HY
  refine ⟨j, ?_⟩
  apply (RegularComponentTransport.joinedIn_restrictPreimage_iff p S t y
    (sections F cone height c B hc h hheight hactive x j t) rfl
      (sections_project F cone height c B hc h hheight hactive x j t)).mpr
  apply (FlatAffineShiftedSlice.joined_fiber_iff F (original c) x h hactive t.val y.val
    (sections F cone height c B hc h hheight hactive x j t).val rfl
      (arc_level F cone height c B hc h hheight hactive x j t.val (Ioo_subset_Icc_self t.property))).mpr
  have HE := arc_value F cone height c B hc h hheight hactive x j t.val (Ioo_subset_Icc_self t.property)
  exact HE.symm ▸ HJ


end LeanCanny.Connectivity.FlatAffineSlabRegularData
