/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CharacteristicNewton
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Parameter-degree bounds from the integer Newton recurrence -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped BigOperators Classical

/-- Degree does not change under multiplication by a nonzero natural scalar. -/
theorem natDegree_nsmul_integer (k : ℕ) (hk : k ≠ 0) (p : Polynomial ℤ) :
    (k • p).natDegree = p.natDegree := by
  rw [nsmul_eq_mul, ← Polynomial.C_eq_natCast]
  exact Polynomial.natDegree_C_mul (by exact_mod_cast hk)

theorem newton_coefficient_parameterDegree_le (D H : ℕ) (c t : ℕ → Polynomial ℤ)
    (hzero : c 0 = 1)
    (hrec : ∀ k < D, (k + 1) • c (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), c (k - j) * t (j + 1)))
    (ht : ∀ j, 1 ≤ j → j ≤ D → (t j).natDegree ≤ j * H)
    (k : ℕ) (hk : k ≤ D) : (c k).natDegree ≤ k * H := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => simp only [hzero, Polynomial.natDegree_one, Nat.zero_mul, le_refl]
    | succ k =>
      rw [← natDegree_nsmul_integer (k + 1) (by omega) (c (k + 1)),
        hrec k (by omega), Polynomial.natDegree_neg]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      exact Polynomial.natDegree_mul_le.trans
        ((Nat.add_le_add (ih (k - j) (by omega) (by omega))
          (ht (j + 1) (by omega) (by omega))).trans_eq
            (by rw [← Nat.add_mul]; congr 1; omega))

/-- Uniform power-trace parameter degrees give a uniform bound on every
 coefficient of the actual characteristic polynomial. -/
theorem charpoly_coefficient_parameterDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial ℤ)) (H : ℕ)
    (ht : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → ((M ^ j).trace).natDegree ≤ H)
    (k : ℕ) : (M.charpoly.coeff k).natDegree ≤ Fintype.card ι * H := by
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
      Polynomial.natDegree_zero]
    exact Nat.zero_le _

end LeanCanny.CountingHierarchy
