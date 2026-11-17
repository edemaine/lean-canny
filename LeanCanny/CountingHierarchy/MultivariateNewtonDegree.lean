/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CharacteristicNewton
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Multivariate parameter degrees from Newton recurrence -/

public section

namespace LeanCanny.CountingHierarchy.MultivariateNewtonDegree

open Polynomial
open scoped BigOperators Classical

variable {τ : Type*}

/-- Degree does not change under multiplication by a nonzero natural scalar. -/
theorem totalDegree_nsmul_integer (k : ℕ) (hk : k ≠ 0) (p : MvPolynomial τ ℤ) :
    (k • p).totalDegree = p.totalDegree := by
  have hs : (k • p).support = p.support := MvPolynomial.support_smul_eq hk p
  unfold MvPolynomial.totalDegree
  rw [hs]

theorem newton_coefficient_parameterDegree_le (D H : ℕ) (c t : ℕ → MvPolynomial τ ℤ)
    (hzero : c 0 = 1)
    (hrec : ∀ k < D, (k + 1) • c (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), c (k - j) * t (j + 1)))
    (ht : ∀ j, 1 ≤ j → j ≤ D → (t j).totalDegree ≤ j * H)
    (k : ℕ) (hk : k ≤ D) : (c k).totalDegree ≤ k * H := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => simp only [hzero, MvPolynomial.totalDegree_one, Nat.zero_mul, le_refl]
    | succ k =>
      rw [← totalDegree_nsmul_integer (k + 1) (by omega) (c (k + 1)),
        hrec k (by omega), MvPolynomial.totalDegree_neg]
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add (ih (k - j) (by omega) (by omega))
          (ht (j + 1) (by omega) (by omega))).trans_eq
            (by rw [← Nat.add_mul]; congr 1; omega))

/-- Uniform power-trace parameter degrees give a uniform bound on every
 coefficient of the actual characteristic polynomial. -/
theorem charpoly_coefficient_parameterDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial τ ℤ)) (H : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → ((M ^ j).trace).totalDegree ≤ H)
    (k : ℕ) : (M.charpoly.coeff k).totalDegree ≤ Fintype.card ι * H := by
  by_cases hk : k ≤ Fintype.card ι
  · have hrev := newton_coefficient_parameterDegree_le (Fintype.card ι) H
      (fun j => M.charpolyRev.coeff j) (fun j => (M ^ j).trace)
      (by rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev])
      (fun j _ => by simpa only [nsmul_eq_mul] using charpolyRev_newton M j)
      (fun j hj hle => (ht j hj hle).trans (by simpa only [Nat.one_mul] using
        (Nat.mul_le_mul_right H hj))) (Fintype.card ι - k) (Nat.sub_le _ _)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk] at hrev
    exact hrev.trans (Nat.mul_le_mul_right H (Nat.sub_le _ _))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega),
      MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

end LeanCanny.CountingHierarchy.MultivariateNewtonDegree
