/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.LinearCombination

/-! # A single degree-decreasing pure-power reduction

Replacing a divisible monomial using c*X_i^d+low=0 preserves its value up to
the common clearing factor c. The replacement strictly lowers total degree
and reads one shifted coefficient of low. No quotient basis is assumed.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicMonomialReduction
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {σ R : Type*} [CommRing R]

noncomputable def residual (e : σ →₀ ℕ) (i : σ) (d : ℕ) : σ →₀ ℕ := e - Finsupp.single i d

theorem residual_add (e : σ →₀ ℕ) (i : σ) (d : ℕ) (he : d ≤ e i) :
    residual e i d + Finsupp.single i d = e :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr he)

theorem residual_degree (e : σ →₀ ℕ) (i : σ) (d : ℕ) (he : d ≤ e i) :
    (residual e i d).degree + d = e.degree := by
  have H := congrArg (fun e : σ →₀ ℕ => e.degree) (residual_add e i d he)
  simpa only [map_add, Finsupp.degree_single] using H

noncomputable def step (low : MvPolynomial σ R) (e : σ →₀ ℕ) (i : σ) (d : ℕ) : MvPolynomial σ R :=
  -(monomial (residual e i d) 1 * low)

theorem step_degree (low : MvPolynomial σ R) (e : σ →₀ ℕ) (i : σ) (d : ℕ)
    (he : d ≤ e i) (hlow : low.totalDegree < d) : (step low e i d).totalDegree < e.degree := by
  rw [step, totalDegree_neg]
  calc
    _ ≤ (residual e i d).degree + low.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le _ _) _)
    _ < (residual e i d).degree + d := Nat.add_lt_add_left hlow _
    _ = e.degree := residual_degree e i d he

theorem step_coefficient (low : MvPolynomial σ R) (e m : σ →₀ ℕ) (i : σ) (d : ℕ) :
    (step low e i d).coeff m =
      if residual e i d ≤ m then -low.coeff (m - residual e i d) else 0 := by
  simp only [step, coeff_neg, coeff_monomial_mul', one_mul]
  split_ifs <;> simp only [neg_zero]

theorem step_eval {K : Type*} [CommRing K] (φ : R →+* K) (low : MvPolynomial σ R)
    (e : σ →₀ ℕ) (i : σ) (d : ℕ) (he : d ≤ e i) (c : R) (x : σ → K)
    (hx : (C c * X i ^ d + low).eval₂ φ x = 0) :
    (step low e i d).eval₂ φ x = φ c * (monomial e (1 : R)).eval₂ φ x := by
  have HM : monomial (residual e i d) (1 : R) * X i ^ d = monomial e (1 : R) := by
    rw [← monomial_add_single, residual_add e i d he]
  have H0 : φ c * x i ^ d + low.eval₂ φ x = 0 := by
    simpa only [eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X] using hx
  have HE := congrArg (fun p : MvPolynomial σ R => p.eval₂ φ x) HM
  simp only [eval₂_mul, eval₂_pow, eval₂_X] at HE
  rw [step, eval₂_neg, eval₂_mul, ← HE]
  linear_combination -((monomial (residual e i d) (1 : R)).eval₂ φ x) * H0

theorem step_mass (low : MvPolynomial σ ℤ) (e : σ →₀ ℕ) (i : σ) (d : ℕ) :
    MvMass.mass (step low e i d) ≤ MvMass.mass low := by
  rw [step, MvMass.neg]
  exact (MvMass.mul_le _ _).trans (by rw [MvMass.monomial, Int.natAbs_one, Nat.one_mul])

end LeanCanny.Algebra.MonicMonomialReduction
