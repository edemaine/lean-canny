/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineScaledSlabObjectiveNonzero
public import LeanCanny.Geometry.ScaledCoordinateIndependence
public import LeanCanny.Encoding.FlatAffineShiftedSingularLift

/-! # Actual scaled coordinate slices are regular on retained open slabs

A singular slice point would lift to a zero-objective root of the exact
sampled power system. Completeness places it on one of the constructed
branches, contradicting its nonzero objective coordinate. The conclusion
holds for every frozen parent and every feasible point in the open slab.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original Index equation)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem Family.shifted_slice_regular_scaled (F : Inputs)
    (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (height : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count (next F) u))
    (c : List Bool) (B : Family (next F) cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language (next F) cone height)
    (h : Fin (arity F (original c)))
    (hheight : height (original c) = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h)
    (scale : Fin (arity F (original c)) → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.succ i =
      scale j * FermatCoordinateCone.normal j i)
    (hactive : h ∈ FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
    (x : FlatAffinePowerSampleInput.OriginalRoots F (original c))
    (t : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c))
    (y : Fin (arity F (original c)) → ℝ) (hy : y ∈ FlatAffineShiftedSlice.slice F (original c) x h t.val) :
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source (original c))
      (FlatAffineFullSourceTower.free F (original c) (F.depth (original c)))
      (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c))) y) := by
  by_contra hsingular
  have HI : ∀ d : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)) → ℝ,
      (∀ i, ∑ j : FlatAffineFullSourceTower.free F (original c) (F.depth (original c)),
        d j * (FlatAffineFullSourceTower.direction F (original c) (F.depth (original c)) j.val.succ i : ℝ) = 0) →
      ∀ j, d j = 0 := by
    intro d hd
    apply ScaledCoordinateIndependence.normals _ (fun j => (scale j : ℝ))
      (fun j => by exact_mod_cast hscale j) d
    intro i
    have H := hd i
    simpa only [hnormal, Int.cast_mul, FermatCoordinateCone.normal, apply_ite, Int.cast_one, Int.cast_zero] using H
  obtain ⟨z, HZ, H0⟩ := FlatAffineShiftedSlice.exists_singular_power_root F (original c) x h hactive t.val y hy HI hsingular
  have HQ : equation (next F) height c t.val z := by
    change ∀ i, (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ) z =
      if i = height (original c) then t.val else 0
    simpa only [hheight] using HZ
  obtain ⟨j, HJ, _⟩ := (B.complete t z).mp HQ
  exact B.newest_objective_ne_zero_scaled F cone height c hc h hheight scale hscale hnormal hactive j t
    ((congrFun HJ (FlatAffinePowerSingularHeightCurves.objectiveIndex F (original c))).trans H0)

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
