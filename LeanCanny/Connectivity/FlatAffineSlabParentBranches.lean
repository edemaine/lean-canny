/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabComponentSampling
public import LeanCanny.Encoding.FlatAffineShiftedRootGeometry

/-! # Complete critical branches for one exact frozen parent

The original ancestor tuple is constant on each closed branch. Filtering the
finite branch family by the stated parent's complete tuple retains exactly
its branches and still meets every component in every interior fiber.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem Family.original_ancestor_constant (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (j : Index (next F) cone height c)
    (r t : Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j r.val) =
      FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j t.val) := by
  let T := Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have HR (r : T) (i : Fin (FlatAffineFullSourcePositive.count (next F) (original c))) :
      (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ) (B.curve j r.val) =
        if i = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h then r.val else 0 := by
    have H := B.roots j r.val r.property
    change ∀ i, (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ)
      (B.curve j r.val) = if i = height (original c) then r.val else 0 at H
    rw [hheight] at H
    exact H i
  let z : T → FlatAffinePowerSampleInput.OriginalRoots F (original c) := fun r =>
    ⟨FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j r.val),
      FlatAffineShiftedSlice.ancestor_roots F (original c) h hactive r.val _ (HR r)⟩
  have HC : Continuous (fun r : T => B.curve j r.val) :=
    continuousOn_iff_continuous_domRestrict.mp (B.continuous j)
  have HZ : Continuous z := (FlatAffineShiftedSlice.continuous_ancestorPoint F (original c) _ HC).subtype_mk _
  let C := FlatAffineCompleteRootStages.cone_prefix (next F) cone F.depth
    (fun u => by change F.depth u ≤ F.depth u + 1; omega)
  let I := FlatAffinePowerSampleInput.input F C
  let : Finite (SquareSampleComplete.Roots I (original c)) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete F C) (original c)).1
  let : Finite (FlatAffinePowerSampleInput.OriginalRoots F (original c)) :=
    Finite.of_equiv (SquareSampleComplete.Roots I (original c)) (FlatAffinePowerSampleInput.originalRootsEquiv F (original c))
  let : TotallyDisconnectedSpace (FlatAffinePowerSampleInput.OriginalRoots F (original c)) := inferInstance
  exact congrArg (fun p : FlatAffinePowerSampleInput.OriginalRoots F (original c) => p.val)
    (TotallyDisconnectedSpace.eq_of_continuous z HZ r t)

def ParentIndex (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u)) (c : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) :=
  {j : Index (next F) cone height c // FlatAffineShiftedSlice.ancestorPoint F (original c) j.val = x.val}

theorem parentIndex_finite (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) : Finite (ParentIndex F cone height c x) := by
  let : Finite (Index (next F) cone height c) := (exists_family (next F) cone height c hc).1
  exact Finite.of_injective (fun j : ParentIndex F cone height c x => j.val) Subtype.val_injective

theorem Family.parent_ancestor (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) (j : ParentIndex F cone height c x)
    (r : Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    FlatAffineShiftedSlice.ancestorPoint F (original c) (B.curve j.val r.val) = x.val := by
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc)
  exact (B.original_ancestor_constant F cone height c h hheight hactive j.val r ⟨_, HT⟩).trans
    ((congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) (B.anchor j.val)).trans j.property)

theorem Family.sample_parent_branch (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
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
    (t : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (y : Fin (arity F (original c)) → ℝ) (hy : y ∈ FlatAffineShiftedSlice.slice F (original c) x h t.val) :
    ∃ j : ParentIndex F cone height c x,
      JoinedIn (FlatAffineShiftedSlice.slice F (original c) x h t.val) y
        (FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val t.val)) := by
  obtain ⟨j, HA, HJ⟩ := B.sample_shifted_slice F cone height c hc h hheight hnormal hactive hobjective x t y hy
  have HT := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between (next F) cone height false c hc)
  have HE := B.original_ancestor_constant F cone height c h hheight hactive j
    ⟨t.val, Ioo_subset_Icc_self t.property⟩ ⟨_, HT⟩
  have HP := HE.trans (congrArg (FlatAffineShiftedSlice.ancestorPoint F (original c)) (B.anchor j))
  exact ⟨⟨j, HP.symm.trans HA⟩, HJ⟩

theorem Family.parent_spatial_mem (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) (j : ParentIndex F cone height c x)
    (r : Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r.val) ∈
      FlatAffineShiftedSlice.slice F (original c) x h r.val := by
  apply FlatAffineShiftedSlice.spatial_mem_slice F (original c) h hactive r.val _ ?_ x
    (B.parent_ancestor F cone height c hc h hheight hactive x j r)
  have HR := B.roots j.val r.val r.property
  change ∀ i, (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ)
    (B.curve j.val r.val) = if i = height (original c) then r.val else 0 at HR
  rw [hheight] at HR
  exact HR

theorem Family.parent_spatial_continuous (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c)) (j : ParentIndex F cone height c x) :
    ContinuousOn (fun r => FlatAffineShiftedSlice.spatialPoint F (original c) (B.curve j.val r))
      (Icc (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have HC := continuousOn_iff_continuous_domRestrict.mp (B.continuous j.val)
  exact continuous_pi (fun i => (continuous_apply
    (FlatAffinePowerTower.current (FlatAffinePowerSingularHeightCurves.lastStage F (original c)) i).castSucc).comp HC)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
