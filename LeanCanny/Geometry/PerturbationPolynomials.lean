/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialPerturbation
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Integer polynomial equations for the perturbation family

Two parameter variables represent epsilon and delta. Spatial and shift variables
are separate blocks. The constraints and squared-radius equation have integer
coefficients; evaluating parameters recovers the compact perturbation sets.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial
open scoped BigOperators

abbrev Variable (ι : Type*) := Sum Bool (Sum ι (Constraint ι))

variable {ι : Type*} [Fintype ι]

noncomputable def spatial (p : MvPolynomial ι ℤ) : MvPolynomial (Variable ι) ℤ :=
  MvPolynomial.rename (fun i => Sum.inr (Sum.inl i)) p

noncomputable def constraintPolynomial (p : MvPolynomial ι ℤ) : Constraint ι → MvPolynomial (Variable ι) ℤ
  | .inl false => spatial p + X (.inr (.inr (.inl false)))
  | .inl true => -spatial p + X (.inr (.inr (.inl true)))
  | .inr (i, false) => X (.inr (.inl i)) + 1 - X (.inl false) + X (.inr (.inr (.inr (i, false))))
  | .inr (i, true) => 1 - X (.inl false) - X (.inr (.inl i)) + X (.inr (.inr (.inr (i, true))))

noncomputable def radiusPolynomial (ι : Type*) [Fintype ι] : MvPolynomial (Variable ι) ℤ :=
  (∑ i : Constraint ι, X (.inr (.inr i)) ^ 2) - X (.inl true) ^ 2

def assignment (epsilon delta : ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ)) : Variable ι → ℝ
  | .inl false => epsilon
  | .inl true => delta
  | .inr (.inl i) => z.1 i
  | .inr (.inr i) => z.2 i

omit [Fintype ι] in
theorem eval_spatial (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    (spatial p).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = p.eval₂ (Int.castRingHom ℝ) z.1 := by
  rw [spatial, MvPolynomial.eval₂_rename]
  rfl

omit [Fintype ι] in
theorem eval_constraint (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) (i : Constraint ι) :
    (constraintPolynomial p i).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = value p epsilon i z.1 + z.2 i := by
  rcases i with b | ⟨j, b⟩ <;> cases b <;>
    simp only [constraintPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_neg,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_X, eval_spatial, assignment, value]

theorem eval_radius (epsilon delta : ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    (radiusPolynomial ι).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = (∑ i, z.2 i ^ 2) - delta ^ 2 := by
  simp only [radiusPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, assignment]

theorem mem_perturbed_iff_polynomials (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) : z ∈ perturbed p epsilon delta ↔
      (∀ i, 0 ≤ (constraintPolynomial p i).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z)) ∧
        (radiusPolynomial ι).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta z) = 0 := by
  simp only [perturbed, Set.mem_ofPred_eq, eval_constraint, eval_radius, sub_eq_zero]

omit [Fintype ι] in
theorem constraint_degree (p : MvPolynomial ι ℤ) (i : Constraint ι) :
    (constraintPolynomial p i).totalDegree ≤ max p.totalDegree 1 := by
  have hp : (spatial p).totalDegree ≤ p.totalDegree := totalDegree_rename_le _ _
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact (totalDegree_add _ _).trans (max_le_max hp (by simp))
  · exact (totalDegree_add _ _).trans (max_le_max (by simpa only [totalDegree_neg] using hp) (by simp))
  · have h1 := totalDegree_add (X (.inr (.inl j)) : MvPolynomial (Variable ι) ℤ) 1
    have h2 := totalDegree_sub (X (.inr (.inl j)) + 1 : MvPolynomial (Variable ι) ℤ) (X (.inl false))
    have h3 := totalDegree_add (X (.inr (.inl j)) + 1 - X (.inl false) : MvPolynomial (Variable ι) ℤ)
      (X (.inr (.inr (.inr (j, false)))))
    simp only [totalDegree_X, totalDegree_one] at h1 h2 h3
    change (_ + _ : MvPolynomial (Variable ι) ℤ).totalDegree ≤ _
    omega
  · have h1 := totalDegree_sub (1 : MvPolynomial (Variable ι) ℤ) (X (.inl false))
    have h2 := totalDegree_sub (1 - X (.inl false) : MvPolynomial (Variable ι) ℤ) (X (.inr (.inl j)))
    have h3 := totalDegree_add (1 - X (.inl false) - X (.inr (.inl j)) : MvPolynomial (Variable ι) ℤ)
      (X (.inr (.inr (.inr (j, true)))))
    simp only [totalDegree_X, totalDegree_one] at h1 h2 h3
    change (_ + _ : MvPolynomial (Variable ι) ℤ).totalDegree ≤ _
    omega

theorem radius_degree (ι : Type*) [Fintype ι] : (radiusPolynomial ι).totalDegree ≤ 2 := by
  have hs : (∑ i : Constraint ι, (X (.inr (.inr i)) : MvPolynomial (Variable ι) ℤ) ^ 2).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (fun _ _ => by simp only [totalDegree_X_pow, Nat.le_refl])
  exact (totalDegree_sub _ _).trans (max_le hs (by simp only [totalDegree_X_pow, Nat.le_refl]))

theorem constraint_card (ι : Type*) [Fintype ι] : Fintype.card (Constraint ι) = 2 + 2 * Fintype.card ι := by
  simp only [Constraint, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  omega

theorem variable_card (ι : Type*) [Fintype ι] : Fintype.card (Variable ι) = 4 + 3 * Fintype.card ι := by
  simp only [Variable, Constraint, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  omega

end LeanCanny.Geometry.PolynomialPerturbation
