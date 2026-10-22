/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SpatialPolynomialCalculus

/-! # Integer polynomial equations for singular radii

For an active set S, the system consists of g_S - delta^2 and all spatial
partial derivatives of g_S. Its common zeros are exactly the critical points
with critical value delta^2. Every singular active fixed-radius point supplies
such a zero. This does not yet establish finiteness of the critical values.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial

variable {ι : Type*}

noncomputable def criticalPolynomial (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) :
    Option ι → MvPolynomial (Variable ι) ℤ
  | none => energyPolynomial p s - X (.inl true) ^ 2
  | some i => pderiv (.inr (.inl i)) (energyPolynomial p s)

theorem criticalPolynomial_degree (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) (j : Option ι) :
    (criticalPolynomial p s j).totalDegree ≤ 2 * max p.totalDegree 1 := by
  cases j with
  | none =>
    apply (totalDegree_sub _ _).trans
    apply max_le (energyPolynomial_degree p s)
    simp only [totalDegree_X_pow]
    omega
  | some i =>
    exact (Algebra.PartialDerivativeDegree.degree_le _ _).trans
      ((Nat.sub_le _ _).trans (energyPolynomial_degree p s))

variable [Fintype ι] [DecidableEq ι]

theorem critical_equations_iff (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    (∀ j, (criticalPolynomial p s j).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = 0) ↔
      ActiveRadius.energy (constraintMap p epsilon) s z.1 = delta ^ 2 ∧
        fderiv ℝ (ActiveRadius.energy (constraintMap p epsilon) s) z.1 = 0 := by
  rw [energy_critical_iff p s epsilon delta z]
  constructor
  · intro h
    refine ⟨?_, fun i => h (some i)⟩
    have hv := h none
    simpa only [criticalPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow,
      MvPolynomial.eval₂_X, assignment, eval_energyPolynomial, sub_eq_zero] using hv
  · rintro ⟨hv, hg⟩ j
    cases j with
    | none =>
      simpa only [criticalPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X, assignment, eval_energyPolynomial, sub_eq_zero] using hv
    | some i => exact hg i

theorem singular_implies_critical_equations (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ))
    (hz : z ∈ perturbed p epsilon delta) (ha : ∀ i ∈ s, parameterMap p epsilon z i = 0)
    (hs : ¬ Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon) s delta) z)) :
    ∀ j, (criticalPolynomial p s j).eval₂ (Int.castRingHom ℝ)
      (assignment epsilon delta (z.1, 0)) = 0 := by
  apply (critical_equations_iff p s epsilon delta (z.1, 0)).mpr
  exact ActiveRadius.singular_implies_critical (constraintMap p epsilon) s delta z
    (((contDiff_constraintMap p epsilon).differentiable (by simp)) z.1) ha hz.2 hs

end LeanCanny.Geometry.PolynomialPerturbation
