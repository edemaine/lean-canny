/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ActiveRadiusCritical
public import LeanCanny.Geometry.PerturbationPolynomials

/-! # Integer polynomials for active sum-of-squares critical values

Subtracting each shift variable recovers the original constraint polynomial.
The active sum of their squares realizes the energy in the singular-radius
criterion, with degree at most twice the original constraint degree bound.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

noncomputable def unshiftedPolynomial (p : MvPolynomial ι ℤ) (i : Constraint ι) : MvPolynomial (Variable ι) ℤ :=
  constraintPolynomial p i - X (.inr (.inr i))

noncomputable def energyPolynomial (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) : MvPolynomial (Variable ι) ℤ :=
  ∑ i ∈ s, unshiftedPolynomial p i ^ 2

theorem eval_unshifted (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) (i : Constraint ι) :
    (unshiftedPolynomial p i).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = value p epsilon i z.1 := by
  rw [unshiftedPolynomial, MvPolynomial.eval₂_sub, eval_constraint, MvPolynomial.eval₂_X]
  simp only [assignment, add_sub_cancel_right]

theorem eval_energyPolynomial (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    (energyPolynomial p s).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) =
      ActiveRadius.energy (constraintMap p epsilon) s z.1 := by
  simp only [energyPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow, eval_unshifted,
    ActiveRadius.energy, constraintMap]

theorem unshifted_degree (p : MvPolynomial ι ℤ) (i : Constraint ι) :
    (unshiftedPolynomial p i).totalDegree ≤ max p.totalDegree 1 := by
  apply (totalDegree_sub _ _).trans
  exact max_le (constraint_degree p i) (by simp only [totalDegree_X]; exact le_max_right _ _)

theorem energyPolynomial_degree (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) :
    (energyPolynomial p s).totalDegree ≤ 2 * max p.totalDegree 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (unshifted_degree p i))

end LeanCanny.Geometry.PolynomialPerturbation
