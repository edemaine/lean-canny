/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeUniformRationalDirections
public import LeanCanny.Geometry.TubeRationalSampling

/-! # Finite positive-inactive tube samples with one rational direction

Choose one rational finite-root direction in the objective-stability
neighborhood of a strict supporting direction. One active set and that
direction then supply suitable samples throughout a small positive interval.
The direction's bit size and the interval's size remain unbounded here.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

variable {ι : Type*} [Fintype ι]

def UniformRationalFiniteProjectionSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι),
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℚ,
      ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        (∀ t : Finset (PolynomialPerturbation.Constraint ι),
          (projectionRootSet p t epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u)).Finite) ∧
            ∃ x ∈ projectionRootSet p s epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u),
              ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

theorem uniform_rational_finite_samples_of_strict (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hv : v (base ι) = 1)
    (hstrict : StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z) :
    UniformRationalFiniteProjectionSamples p epsilon delta := by
  obtain ⟨U, hU, a, ha, hsamples⟩ := exists_sample_neighborhood_of_strict p epsilon delta v z hd hz hstrict
  obtain ⟨u, hu, b, hb, hfinite⟩ := exists_uniform_rational_finite_direction_near p epsilon delta v hv U hU
  refine ⟨PolynomialPerturbation.activeSet p epsilon z, u, min a b, lt_min ha hb, ?_⟩
  intro alpha hp hl
  exact ⟨hfinite alpha hp (hl.trans_le (min_le_right _ _)),
    hsamples alpha hp (hl.trans_le (min_le_left _ _)) _ hu (ProjectionCritical.rationalDirection_base (base ι) u)⟩

theorem uniform_rational_finite_samples_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    UniformRationalFiniteProjectionSamples p epsilon delta := by
  obtain ⟨v, z, hz, hv, hstrict⟩ := exists_strict_supporting_maximum p epsilon delta he hd.le hn
  exact uniform_rational_finite_samples_of_strict p epsilon delta v z hd hz hv hstrict

theorem rational_finite_samples_of_uniform (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : UniformRationalFiniteProjectionSamples p epsilon delta) : EventualRationalFiniteProjectionSamples p epsilon delta := by
  obtain ⟨s, u, a, ha, hr⟩ := h
  exact ⟨s, a, ha, fun alpha hp hl => ⟨u, hr alpha hp hl⟩⟩

theorem nonempty_iff_uniform_rational_finite_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ UniformRationalFiniteProjectionSamples p epsilon delta :=
  ⟨uniform_rational_finite_samples_of_feasible p epsilon delta he hd,
    fun h => (nonempty_iff_eventual_rational_finite_samples p epsilon delta he hd).mpr
      (rational_finite_samples_of_uniform p epsilon delta h)⟩

end LeanCanny.Geometry.TubePolynomial
