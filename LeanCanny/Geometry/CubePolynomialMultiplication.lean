/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CubeCoefficientFormula
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.Ring

/-! # Multiplication commutes with rational compactification

Fixed denominator allowances add when multiplying polynomials that fit them.
For integer polynomials, actual coordinate degrees add for nonzero products.
Thus the existing compactification commutes with multiplication and squaring,
including zero polynomials. A short squared source supplies its dense square.
-/

@[expose] public section

namespace LeanCanny.Geometry.CubePolynomial
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem clearHom_mul (D E : ι → ℕ) (p q : MvPolynomial ι R)
    (hp : ∀ e ∈ p.support, ∀ i, e i ≤ 2 * D i)
    (hq : ∀ e ∈ q.support, ∀ i, e i ≤ 2 * E i) :
    clearHom (fun i => D i + E i) (p * q) = clearHom D p * clearHom E q := by
  classical
  change clearHom (fun i => D i + E i) (p * q) =
    (∑ e ∈ p.support, C (p.coeff e) * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)) *
      (∑ e ∈ q.support, C (q.coeff e) * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * E i - e i))
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial, clearHom_monomial]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro e he
  rw [map_mul]
  have hprod : (∏ i, (X i : MvPolynomial ι R) ^ (e + f) i * (1 - X i ^ 2) ^ (2 * (D i + E i) - (e + f) i)) =
      ∏ i, (X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)) *
        (X i ^ f i * (1 - X i ^ 2) ^ (2 * E i - f i)) := by
    apply Finset.prod_congr rfl
    intro i _
    have hei := hp e he i
    have hfi := hq f hf i
    have hsub : 2 * (D i + E i) - (e i + f i) = (2 * D i - e i) + (2 * E i - f i) := by omega
    simp only [Finsupp.add_apply, hsub, pow_add]
    ring
  rw [hprod, Finset.prod_mul_distrib]
  ring

theorem cleared_zero : cleared (0 : MvPolynomial ι ℤ) = 0 := by simp [cleared]

theorem cleared_mul (p q : MvPolynomial ι ℤ) : cleared (p * q) = cleared p * cleared q := by
  by_cases hp : p = 0
  · simp [hp, cleared_zero]
  by_cases hq : q = 0
  · simp [hq, cleared_zero]
  have hd : (p * q).degreeOf = fun i => p.degreeOf i + q.degreeOf i := by
    funext i
    exact MvPolynomial.degreeOf_mul_eq hp hq
  rw [← clearHom_eq_cleared, hd, clearHom_mul]
  · rfl
  · intro e he i
    exact (MvPolynomial.monomial_le_degreeOf i he).trans (by omega)
  · intro e he i
    exact (MvPolynomial.monomial_le_degreeOf i he).trans (by omega)

theorem cleared_one : cleared (1 : MvPolynomial ι ℤ) = 1 := by simp [cleared]

theorem cleared_pow (p : MvPolynomial ι ℤ) (n : ℕ) : cleared (p ^ n) = cleared p ^ n := by
  induction n with
  | zero => simp only [pow_zero, cleared_one]
  | succ n ih => rw [pow_succ, cleared_mul, ih, pow_succ]

theorem cleared_sq (p : MvPolynomial ι ℤ) : cleared (p ^ 2) = cleared p ^ 2 := by
  simpa only [pow_two] using cleared_mul p p

end LeanCanny.Geometry.CubePolynomial
