/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IntegerProjectionDirections
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Common integer directions for the actual small active tubes

At every sufficiently small positive tube level, one normalized direction
with natural-number coordinates gives finite integer projection root sets
for every active set. The finite grid bound may depend on the real parameters
and level; no input-size bound or positive-inactive sample is asserted here.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

variable {ι : Type*} [Fintype ι]

theorem exists_nat_finite_tube_directions (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ b : ℕ, ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℕ,
        (∀ i, u i ≤ b) ∧ ∀ s : Finset (PolynomialPerturbation.Constraint ι),
          (projectionRootSet p s epsilon delta alpha
            (Algebra.ProjectionFiniteSpecialization.normalizedDirection (base ι) (fun i => (u i : ℝ)))).Finite := by
  classical
  obtain ⟨a, ha, hr⟩ := exists_common_regular_interval p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨b, u, hu, hfinite⟩ := ProjectionCritical.exists_common_nat_direction_of_coefficients
    (coefficientMap epsilon delta alpha) (fun s => polynomial p s) (base ι)
    (fun s x hx => hr alpha hp hs s x hx)
  refine ⟨b, u, hu, ?_⟩
  intro s
  apply (hfinite s).subset
  intro x hx j
  have h := hx j
  rw [eval_integerProjection] at h
  exact h

end LeanCanny.Geometry.TubePolynomial
