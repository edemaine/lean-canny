/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # The differential equation of a finite polynomial exponential -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial
open scoped Classical BigOperators

variable {K : Type*} [Field K]

/-- The exponential sum truncated in its power index. -/
@[expose] noncomputable def finiteExponential (D : ℕ) (G : K[X]) : K[X] :=
  ∑ j ∈ Finset.range (D + 1), C ((j.factorial : K)⁻¹) * G ^ j

theorem inverse_factorial_succ (j : ℕ) (hj : (j + 1 : ℕ) ≠ (0 : K)) :
    (((j + 1).factorial : K)⁻¹) * (j + 1 : ℕ) = ((j.factorial : K)⁻¹) := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hj, mul_one]

/-- Differentiation cancels factorials whenever the relevant integers
 are nonzero in the coefficient field. -/
theorem derivative_finiteExponential (D : ℕ) (G : K[X])
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) :
    derivative (finiteExponential D G) =
      derivative G * ∑ j ∈ Finset.range D, C ((j.factorial : K)⁻¹) * G ^ j := by
  rw [finiteExponential, derivative_sum, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, derivative_C, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow_succ]
  have hf := inverse_factorial_succ (K := K) j (hK (j + 1) (by omega)
    (by have := Finset.mem_range.mp hj; omega))
  calc
    _ = C ((((j + 1).factorial : K)⁻¹) * (j + 1 : ℕ)) * G ^ j * derivative G := by
      rw [map_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by rw [hf]; ring

/-- The differential equation holds modulo `X^D`; no infinite power
 series or rational-to-finite-field map is used. -/
theorem finiteExponential_differential_error (D : ℕ) (G : K[X])
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) :
    derivative (finiteExponential D G) - derivative G * finiteExponential D G =
      -(derivative G * C ((D.factorial : K)⁻¹) * G ^ D) := by
  rw [derivative_finiteExponential D G hK]
  conv_lhs => rhs; rw [finiteExponential, Finset.sum_range_succ]
  ring

theorem finiteExponential_differential_coeff (D : ℕ) (G : K[X])
    (hG : G.coeff 0 = 0) (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0)
    (k : ℕ) (hk : k < D) :
    (derivative (finiteExponential D G)).coeff k =
      (derivative G * finiteExponential D G).coeff k := by
  have hdiv : (X : K[X]) ^ D ∣
      derivative (finiteExponential D G) - derivative G * finiteExponential D G := by
    rw [finiteExponential_differential_error D G hK]
    apply dvd_neg.mpr
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG) D) _
  have hz := X_pow_dvd_iff.mp hdiv k hk
  simpa only [coeff_sub, sub_eq_zero] using hz

/-- The constant coefficient is normalized when the exponent has zero
 constant term. -/
theorem finiteExponential_coeff_zero (D : ℕ) (G : K[X]) (hG : G.coeff 0 = 0) :
    (finiteExponential D G).coeff 0 = 1 := by
  have hpow (j : ℕ) : (G ^ j).coeff 0 = G.coeff 0 ^ j := by
    rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
  unfold finiteExponential
  simp only [finsetSum_coeff, coeff_C_mul, hpow, hG]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

end LeanCanny.CountingHierarchy
