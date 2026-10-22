/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeFeasibility

/-! # No false positives from vanishing integer projection-system samples

The level equation is the first row of every expanded projection system.
Consequently arbitrarily small roots with nonnegative inactive constraints
give a feasible point. Active sets and directions may vary between samples.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

variable {ι : Type*} [Fintype ι]

theorem sample_of_integer_roots (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (x v : Coordinate ι → ℝ)
    (hroots : ∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0)
    (hinactive : ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i) :
    Sample p epsilon delta s alpha x := by
  refine ⟨?_, hinactive⟩
  have h := hroots none
  rw [eval_integerProjection] at h
  change (Algebra.ProjectionEquations.polynomial (polynomial p s) (base ι) none).eval₂
    (coefficientMap epsilon delta alpha) (Sum.elim x v) = 0 at h
  rw [Algebra.ProjectionEquations.eval_level] at h
  exact h

def SmallProjectionSamples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∀ b : ℝ, 0 < b → ∃ alpha : ℝ, 0 < alpha ∧ alpha < b ∧
    ∃ (s : Finset (PolynomialPerturbation.Constraint ι)) (x v : Coordinate ι → ℝ),
      (∀ j, (integerProjection p s j).eval₂ (Int.castRingHom ℝ)
        (Sum.elim (Sum.elim x v) (parameters epsilon delta alpha)) = 0) ∧
      ∀ i, i ∉ s → 0 ≤ PolynomialPerturbation.parameterMap p epsilon (splitPoint x) i

theorem small_samples_of_projection (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (h : SmallProjectionSamples p epsilon delta) : SmallSamples p epsilon delta := by
  intro b hb
  obtain ⟨alpha, hp, hs, s, x, v, hr, hi⟩ := h b hb
  exact ⟨alpha, hp, hs, s, x, sample_of_integer_roots p s epsilon delta alpha x v hr hi⟩

theorem feasible_of_small_projection_samples (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (h : SmallProjectionSamples p epsilon delta) :
    (PolynomialPerturbation.perturbed p epsilon delta).Nonempty :=
  feasible_of_small_samples p epsilon delta he hd (small_samples_of_projection p epsilon delta h)

end LeanCanny.Geometry.TubePolynomial
