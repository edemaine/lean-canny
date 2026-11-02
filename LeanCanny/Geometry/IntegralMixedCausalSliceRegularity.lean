/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCausalLevelRegularity
public import LeanCanny.Geometry.FlatCoordinateConstraintRegularity

/-! # Actual canonical source-and-frozen-height constraint regularity

The causal level derivative supplies the missing free pivot. The literal
integer scales in the current CriticalData are nonzero, so the source and all
active old-height constraints have a surjective derivative. This is precisely
the constrained-extremum premise, not a Hessian or critical-curve assertion.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCanonicalDilation
open scoped Classical
variable {n S B m : ℕ} {ι : Type}

theorem canonical_slice_surjective (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht)
      (coefficient n D R G)) S B m ι) (hm : m≤S) (hkn : k≤n) (select : Fin k → Fin m)
    (q : Fin (n+1) → ℝ) (v : ℝ) (hv : v∈Set.Icc (-1:ℝ) 1) :
    let d := data x hm (rule hkn select).critical
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (FermatCriticalHomogenization.polynomial d.low d.leading d.degree) d.frozen
      (PhysicalPowerCriticalRows.coordinateNormals d.objective d.scales d.free) (Fin.snoc q v)) := by
  dsimp only
  apply FlatCoordinateConstraintRegularity.surjective _ _ _ _ (data x hm (rule hkn select).critical).scales_ne
    _ (Fin.last (n+1))
  · intro H
    have HH := (Finset.mem_filter.mp H).2
    change n+1<k+1 at HH
    omega
  · exact ne_of_lt (level_derivative_neg k D R G u t ht q v hv)

end LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
