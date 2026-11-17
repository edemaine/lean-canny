/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CharacteristicNewton
public import LeanCanny.CountingHierarchy.FiniteExponential
public import LeanCanny.CountingHierarchy.TraceExponential
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Identifying the finite exponential with characteristic coefficients -/

public section

namespace LeanCanny.CountingHierarchy

open Matrix Polynomial
open scoped Classical BigOperators

variable {K : Type*} [Field K]

theorem coefficientPolynomial_coeff (D : ℕ) (c : ℕ → K) (k : ℕ) (hk : k ≤ D) :
    (coefficientPolynomial D c).coeff k = c k := by
  unfold coefficientPolynomial
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  simp only [Finset.sum_ite_eq, Finset.mem_range, show k < D + 1 by omega, ↓reduceIte]

/-- Newton recurrence determines all coefficients through a degree where
 its integer multipliers are nonzero. -/
theorem coefficients_eq_of_newton (D : ℕ) (t : ℕ → K) (P Q : K[X])
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0)
    (hzero : P.coeff 0 = Q.coeff 0)
    (hP : ∀ k < D, (k + 1 : ℕ) * P.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), P.coeff (k - j) * t (j + 1)))
    (hQ : ∀ k < D, (k + 1 : ℕ) * Q.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), Q.coeff (k - j) * t (j + 1)))
    (k : ℕ) (hk : k ≤ D) : P.coeff k = Q.coeff k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => exact hzero
    | succ k =>
      apply mul_left_cancel₀ (hK (k + 1) (by omega) hk)
      rw [hP k (by omega), hQ k (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j) (by omega) (by omega)]

theorem trace_logarithm_derivative_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k < D) :
    (derivative (coefficientPolynomial D (fun j => -(M ^ j).trace / (j : K)))).coeff k =
      -(M ^ (k + 1)).trace := by
  rw [coeff_derivative, coefficientPolynomial_coeff D _ (k + 1) (by omega)]
  convert div_mul_cancel₀ (-(M ^ (k + 1)).trace) (hK (k + 1) (by omega) (by omega)) using 1;
    simp only [Nat.cast_add, Nat.cast_one]

/-- The explicit finite exponential satisfies Newton's recurrence in
 every field whose small integer denominators are nonzero. -/
theorem trace_exponential_newton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k < D) :
    (k + 1 : ℕ) * (truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1),
        (truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff (k - j) *
          (M ^ (j + 1)).trace) := by
  let G := coefficientPolynomial D (fun j => -(M ^ j).trace / (j : K))
  have hG : G.coeff 0 = 0 := by rw [coefficientPolynomial_coeff D _ 0 (by omega)]; simp
  have h := finiteExponential_differential_coeff D G hG hK k hk
  change (derivative (truncatedExponential D (fun j => -(M ^ j).trace / (j : K)))).coeff k =
    (derivative G * truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff k at h
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hsum : (∑ j ∈ Finset.range (k + 1),
      (derivative G).coeff j *
        (truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff (k - j)) =
      -(∑ j ∈ Finset.range (k + 1),
        (truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff (k - j) *
          (M ^ (j + 1)).trace) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (derivative G).coeff j = -(M ^ (j + 1)).trace from
      trace_logarithm_derivative_coeff M D hK j (by have := Finset.mem_range.mp hj; omega)]
    ring
  exact (by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h.trans hsum)

/-- The finite exponential has exactly the characteristic coefficients
 through the requested truncation degree. -/
theorem trace_exponential_coeff_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ D) :
    (truncatedExponential D (fun j => -(M ^ j).trace / (j : K))).coeff k =
      M.charpolyRev.coeff k := by
  apply coefficients_eq_of_newton D (fun j => (M ^ j).trace) _ _ hK ?_
    (trace_exponential_newton M D hK) (fun j _ => charpolyRev_newton M j) k hk
  have hG : (coefficientPolynomial D (fun j => -(M ^ j).trace / (j : K))).coeff 0 = 0 := by
    rw [coefficientPolynomial_coeff D _ 0 (by omega)]
    simp
  change (finiteExponential D _).coeff 0 = M.charpolyRev.coeff 0
  rw [finiteExponential_coeff_zero D _ hG, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-- Reversal turns the constructed exponential coefficients into the
 actual characteristic polynomial coefficients of the matrix. -/
theorem trace_exponential_coeff_eq_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K)
    (hK : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → (j : K) ≠ 0)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (truncatedExponential (Fintype.card ι)
      (fun j => -(M ^ j).trace / (j : K))).coeff (Fintype.card ι - k) = M.charpoly.coeff k := by
  rw [trace_exponential_coeff_eq_charpolyRev M _ hK _ (Nat.sub_le _ _),
    ← Matrix.reverse_charpoly, coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
    revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk]

end LeanCanny.CountingHierarchy
