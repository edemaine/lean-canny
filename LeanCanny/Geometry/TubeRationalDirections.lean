/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RationalProjectionDirections
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Dense rational finite-root directions for the actual active tubes

At every sufficiently small positive tube level, every neighborhood of a
normalized direction contains a rational direction giving finite root sets
for all active sets. Numerator and denominator bounds are not supplied.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set
open scoped Topology

variable {ι : Type*} [Fintype ι]

theorem exists_rational_finite_directions_near (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ v : Coordinate ι → ℝ, v (base ι) = 1 →
        ∀ U : Set (Coordinate ι → ℝ), U ∈ nhds v →
          ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℚ,
            ProjectionCritical.rationalDirection (base ι) u ∈ U ∧
              ∀ s : Finset (PolynomialPerturbation.Constraint ι),
                (projectionRootSet p s epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u)).Finite := by
  classical
  obtain ⟨a, ha, hr⟩ := exists_common_regular_interval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs v hv U hU
  obtain ⟨u, hu, hfinite⟩ := ProjectionCritical.exists_common_rational_direction_near_of_coefficients
    (coefficientMap epsilon delta alpha) (fun s => polynomial p s) (base ι)
    (fun s x hx => hr alpha hp hs s x hx) v hv U hU
  refine ⟨u, hu, ?_⟩
  intro s
  apply (hfinite s).subset
  intro x hx j
  have h := hx j
  rw [eval_integerProjection] at h
  exact h

end LeanCanny.Geometry.TubePolynomial
