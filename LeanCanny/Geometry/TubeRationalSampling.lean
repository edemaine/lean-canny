/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeRationalDirections
public import LeanCanny.Geometry.TubeFiniteSampling

/-! # Positive-inactive finite tube samples with rational directions

Rational finite-root directions can approximate a strict supporting direction,
so uniform objective control preserves positive inactive signs. One active set
works at every sufficiently small level, with rational direction witnesses
allowed to vary with the level. No bit-size or effective parameter bound is
provided.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set

variable {ι : Type*} [Fintype ι]

def EventualRationalFiniteProjectionSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∃ s : Finset (PolynomialPerturbation.Constraint ι), ∃ a : ℝ, 0 < a ∧
    ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℚ,
        (∀ t : Finset (PolynomialPerturbation.Constraint ι),
          (projectionRootSet p t epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u)).Finite) ∧
            ∃ x ∈ projectionRootSet p s epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u),
              ∀ i, i ∉ s → 0 < PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

theorem nearby_rational_finite_directions (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    NearbyFiniteProjectionDirections (ProjectionCritical.IsRationalDirection (base ι)) p epsilon delta := by
  obtain ⟨a, ha, hr⟩ := exists_rational_finite_directions_near p epsilon delta
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs v hv U hU
  obtain ⟨u, hu, hfinite⟩ := hr alpha hp hs v hv U hU
  exact ⟨ProjectionCritical.rationalDirection (base ι) u, hu, ProjectionCritical.rationalDirection_base (base ι) u,
    ⟨u, rfl⟩, hfinite⟩

theorem eventual_rational_finite_samples_of_feasible (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty) :
    EventualRationalFiniteProjectionSamples p epsilon delta := by
  have h := eventual_finite_samples_with_of_feasible (ProjectionCritical.IsRationalDirection (base ι))
    p epsilon delta he hd hn (nearby_rational_finite_directions p epsilon delta)
  obtain ⟨s, a, ha, hr⟩ := h
  refine ⟨s, a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨v, _, hu, hfinite, x, hx, hi⟩ := hr alpha hp hs
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, hfinite, x, hx, hi⟩

theorem finite_samples_of_rational (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : EventualRationalFiniteProjectionSamples p epsilon delta) : EventualFiniteProjectionSamples p epsilon delta := by
  obtain ⟨s, a, ha, hr⟩ := h
  refine ⟨s, a, ha, ?_⟩
  intro alpha hp hs
  obtain ⟨u, hfinite, x, hx, hi⟩ := hr alpha hp hs
  exact ⟨ProjectionCritical.rationalDirection (base ι) u, ProjectionCritical.rationalDirection_base (base ι) u,
    hfinite, x, hx, hi⟩

theorem nonempty_iff_eventual_rational_finite_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 < delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty ↔ EventualRationalFiniteProjectionSamples p epsilon delta :=
  ⟨eventual_rational_finite_samples_of_feasible p epsilon delta he hd,
    fun h => (nonempty_iff_eventual_finite_samples p epsilon delta he hd).mpr (finite_samples_of_rational p epsilon delta h)⟩

end LeanCanny.Geometry.TubePolynomial
