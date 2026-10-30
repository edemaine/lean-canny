/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabCoordinateTests
public import LeanCanny.Encoding.FlatAffineScaledPowerSingularHeightCurves

/-! # Nonzero newest objective multipliers on retained scaled coordinate slabs

The native exceptional polynomial makes coordinate zero tests constant on
each open branch. If its objective multiplier vanished once, coarsening
would force every height on the interval to coincide. Thus every retained
branch has nonzero objective multiplier throughout its interior.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem Family.newest_objective_ne_zero_scaled (F : Inputs)
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
    (j : Index (next F) cone height c)
    (t : Ioo (endpointValue (next F) cone height false c) (endpointValue (next F) cone height true c)) :
    B.curve j t.val (FlatAffinePowerSingularHeightCurves.objectiveIndex F (original c)) ≠ 0 := by
  intro ht
  let a := endpointValue (next F) cone height false c
  let b := endpointValue (next F) cone height true c
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  let v : Ioo a b := ⟨(t.val + b) / 2, by constructor <;> dsimp only [a, b] at * <;> linarith [t.property.1, t.property.2]⟩
  have HC : Continuous (fun r : Ioo a b => B.curve j r.val) :=
    continuousOn_iff_continuous_domRestrict.mp ((B.continuous j).mono Ioo_subset_Icc_self)
  have HZ (r : Ioo a b) : B.curve j r.val (FlatAffinePowerSingularHeightCurves.objectiveIndex F (original c)) = 0 :=
    (B.coordinate_tests_iff hc j (FlatAffinePowerSingularHeightCurves.objectiveIndex F (original c)) t r).1.mp ht
  have HR (r : Ioo a b) (i : Fin (FlatAffineFullSourcePositive.count (next F) (original c))) :
      (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ) (B.curve j r.val) =
        if i = FlatAffinePowerSingularHeightCurves.rowIndex F (original c) h then r.val else 0 := by
    have H := B.roots j r.val (Ioo_subset_Icc_self r.property)
    change ∀ i, (FlatAffinePowerPositive.system (next F) (original c) i).eval₂ (Int.castRingHom ℝ)
      (B.curve j r.val) = if i = height (original c) then r.val else 0 at H
    rw [hheight] at H
    exact H i
  let C := FlatAffineCompleteRootStages.cone_prefix (next F) cone F.depth
    (fun u => by change F.depth u ≤ F.depth u + 1; omega)
  have HE := FlatAffineScaledPowerSingularHeightCurves.parameter_constant F C (original c) h scale hscale hnormal hactive
    (fun r : Ioo a b => r.val) (fun r => B.curve j r.val) HC HZ HR t v
  change t.val = (t.val + b) / 2 at HE
  linarith [t.property.2]

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
