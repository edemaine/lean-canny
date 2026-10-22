/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubePolynomial
public import LeanCanny.Algebra.PolynomialMapDegree
import Lean.Elab.Tactic.Omega

/-! # Point-variable degree bounds for the active tube

Epsilon, delta, and alpha are coefficient variables. These degree bounds count
the spatial and shift variables; projection equations also count directions.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial

variable {ι : Type*}

theorem spatial_degree (p : MvPolynomial ι ℤ) : (spatial p).totalDegree ≤ p.totalDegree :=
  (totalDegree_rename_le _ _).trans (Algebra.PolynomialMapDegree.degree_le _ _)

theorem constraint_degree (p : MvPolynomial ι ℤ) (i : PolynomialPerturbation.Constraint ι) :
    (constraint p i).totalDegree ≤ max p.totalDegree 1 := by
  have hp := spatial_degree p
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact (totalDegree_add _ _).trans (max_le_max hp (by simp))
  · exact (totalDegree_add _ _).trans (max_le_max (by simpa only [totalDegree_neg] using hp) (by simp))
  · have h1 := totalDegree_add (X (.inl j) : MvPolynomial (Coordinate ι) Coefficient) 1
    have h2 := totalDegree_sub (X (.inl j) + 1 : MvPolynomial (Coordinate ι) Coefficient) (C (X (some false)))
    have h3 := totalDegree_add (X (.inl j) + 1 - C (X (some false)) : MvPolynomial (Coordinate ι) Coefficient)
      (X (.inr (.inr (j, false))))
    simp only [totalDegree_X, totalDegree_one, totalDegree_C] at h1 h2 h3
    change (_ + _ : MvPolynomial (Coordinate ι) Coefficient).totalDegree ≤ _
    omega
  · have h1 := totalDegree_sub (1 : MvPolynomial (Coordinate ι) Coefficient) (C (X (some false)))
    have h2 := totalDegree_sub (1 - C (X (some false)) : MvPolynomial (Coordinate ι) Coefficient) (X (.inl j))
    have h3 := totalDegree_add (1 - C (X (some false)) - X (.inl j) : MvPolynomial (Coordinate ι) Coefficient)
      (X (.inr (.inr (j, true))))
    simp only [totalDegree_X, totalDegree_one, totalDegree_C] at h1 h2 h3
    change (_ + _ : MvPolynomial (Coordinate ι) Coefficient).totalDegree ≤ _
    omega

variable [Fintype ι]

theorem radius_degree : (radius ι).totalDegree ≤ 2 := by
  have hs : (∑ i : PolynomialPerturbation.Constraint ι,
      (X (.inr i) : MvPolynomial (Coordinate ι) Coefficient) ^ 2).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (fun _ _ => by simp)
  have hc : ((C (X (some true)) : MvPolynomial (Coordinate ι) Coefficient) ^ 2).totalDegree ≤ 2 := by
    exact (totalDegree_pow _ _).trans (by simp)
  exact (totalDegree_sub _ _).trans (max_le hs hc)

theorem energy_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    (energy p s).totalDegree ≤ 2 * max p.totalDegree 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (radius_degree.trans (le_max_right _ _)))
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 ((constraint_degree p i).trans
      (max_le_max_left _ (by omega))))

theorem polynomial_degree (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι)) :
    (polynomial p s).totalDegree ≤ 2 * max p.totalDegree 2 := by
  exact (totalDegree_sub _ _).trans (max_le (energy_degree p s) (by simp))

end LeanCanny.Geometry.TubePolynomial
