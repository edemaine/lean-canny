/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialDifference
public import Mathlib.Algebra.Ring.GeomSum

/-! # Divided differences of a pure power -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The polynomial quotient of `x^ell - Y^ell` by `x - Y`, with
 `ell = d + 1`. -/
@[expose] noncomputable def purePowerDifference (x : A) (i : Fin n) (d : ℕ) :
    MvPolynomial (Fin n) A :=
  ∑ k ∈ Finset.range (d + 1), C (x ^ (d - k)) * X i ^ k

theorem purePowerDifference_mul (x : A) (i : Fin n) (d : ℕ) :
    purePowerDifference x i d * (C x - X i) = C (x ^ (d + 1)) - X i ^ (d + 1) := by
  have h := (Commute.all (X i : MvPolynomial (Fin n) A) (C x)).geom_sum₂_mul (d + 1)
  have heq : (∑ k ∈ Finset.range (d + 1), X i ^ k * C x ^ (d + 1 - 1 - k)) =
      purePowerDifference x i d := by
    simp only [purePowerDifference, Nat.add_sub_cancel, ← map_pow, mul_comm]
  rw [heq, ← map_pow] at h
  linear_combination -h

theorem purePowerDifference_degree (x : A) (i : Fin n) (d : ℕ) :
    (purePowerDifference x i d).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro k hk
  have hX : (X i ^ k : MvPolynomial (Fin n) A).totalDegree ≤ k := by
    rw [X_pow_eq_monomial]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hm := totalDegree_mul (C (x ^ (d - k))) (X i ^ k)
  rw [totalDegree_C] at hm
  have hk' := Finset.mem_range.mp hk
  omega

theorem purePowerDifference_lower_degree (x : A) (i : Fin n) {d : ℕ} (hd : 1 ≤ d) :
    (purePowerDifference x i d - X i ^ d).totalDegree < d := by
  have heq : purePowerDifference x i d - X i ^ d =
      ∑ k ∈ Finset.range d, C (x ^ (d - k)) * X i ^ k := by
    simp only [purePowerDifference, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      C_1, one_mul, add_sub_cancel_right]
  rw [heq]
  apply lt_of_le_of_lt (totalDegree_finsetSum_le (d := d - 1) ?_) (by omega)
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hX : (X i ^ k : MvPolynomial (Fin n) A).totalDegree ≤ k := by
    rw [X_pow_eq_monomial]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  have hm := totalDegree_mul (C (x ^ (d - k))) (X i ^ k)
  rw [totalDegree_C] at hm
  omega

theorem purePowerDifference_diagonal (x : Fin n → A) (i : Fin n) (d : ℕ) :
    eval x (purePowerDifference (x i) i d) = (d + 1 : ℕ) * x i ^ d := by
  unfold purePowerDifference
  rw [map_sum]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
      eval x (C (x i ^ (d - k)) * X i ^ k) = x i ^ d := by
    simp only [map_mul, eval_C, map_pow, eval_X, ← pow_add]
    congr 1
    have := Finset.mem_range.mp hk
    omega
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end LeanCanny.CountingHierarchy
