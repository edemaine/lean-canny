/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabSliceRegularity
public import LeanCanny.Geometry.FlatAffineShiftedComponentSampling
public import LeanCanny.Encoding.FlatAffineShiftedSliceCompact
public import LeanCanny.Encoding.FlatAffineShiftedRootLift

/-! # Retained actual branches meet every component of every varying slice

Compactness and the proved slab regularity give a path from each feasible
point to a shifted critical root. Its exact lift belongs to a constructed
branch with precisely the stated frozen ancestry. The component sampling
claim therefore concerns the whole original slice, not just the root curve.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original Index equation)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem Family.sample_shifted_slice (F : Inputs)
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
    (fun z hz => B.shifted_slice_regular F cone height c hc h hheight hnormal hactive x t z hz)
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

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
