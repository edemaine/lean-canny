/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AdditiveSubmersion
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.BigOperators.Pi

/-! # Analytic derivatives from formal polynomial partial derivatives

Evaluation of a multivariate polynomial has derivative given by its evaluated
formal partial derivatives. In particular, analytic critical points are exactly
the common zeros of these partial derivatives, including in dimension zero.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialCalculus
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

noncomputable def derivative (φ : R →+* ℝ) (p : MvPolynomial ι R) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (pderiv i p).eval₂ φ x • ContinuousLinearMap.proj i

theorem derivative_apply (φ : R →+* ℝ) (p : MvPolynomial ι R) (x h : ι → ℝ) :
    derivative φ p x h = ∑ i, (pderiv i p).eval₂ φ x * h i := by
  simp [derivative]

theorem derivative_C (φ : R →+* ℝ) (c : R) (x : ι → ℝ) : derivative φ (C c) x = 0 := by
  simp [derivative]

theorem derivative_add (φ : R →+* ℝ) (p q : MvPolynomial ι R) (x : ι → ℝ) :
    derivative φ (p + q) x = derivative φ p x + derivative φ q x := by
  simp [derivative, add_smul, Finset.sum_add_distrib]

theorem derivative_mul_X (φ : R →+* ℝ) (p : MvPolynomial ι R) (j : ι) (x : ι → ℝ) :
    derivative φ (p * X j) x = x j • derivative φ p x + p.eval₂ φ x • ContinuousLinearMap.proj j := by
  classical
  have he (i : ι) : (pderiv i (p * X j)).eval₂ φ x =
      x j * (pderiv i p).eval₂ φ x + if i = j then p.eval₂ φ x else 0 := by
    rw [pderiv_mul, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    by_cases h : i = j <;> simp [pderiv_X, h, mul_comm]
  ext h
  simp only [derivative_apply, he, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, add_mul, Finset.sum_add_distrib]
  simp [mul_assoc, ← Finset.mul_sum, ite_mul]

theorem hasFDerivAt (φ : R →+* ℝ) (p : MvPolynomial ι R) (x : ι → ℝ) :
    HasFDerivAt (fun y => p.eval₂ φ y) (derivative φ p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C, derivative_C] using hasFDerivAt_const (φ c) x
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add, derivative_add] using hp.fun_add hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, derivative_mul_X, add_comm] using
      hp.fun_mul (hasFDerivAt_apply (𝕜 := ℝ) i x)

theorem fderiv_eq (φ : R →+* ℝ) (p : MvPolynomial ι R) (x : ι → ℝ) :
    fderiv ℝ (fun y => p.eval₂ φ y) x = derivative φ p x := (hasFDerivAt φ p x).fderiv

variable [DecidableEq ι]

theorem linear_eq_zero_iff (D : (ι → ℝ) →L[ℝ] ℝ) :
    D = 0 ↔ ∀ i, D (Pi.single i 1) = 0 := by
  constructor
  · intro h i
    simp [h]
  · intro h
    ext x
    rw [pi_eq_sum_univ' x, map_sum]
    simp only [map_smul, h, smul_zero, Finset.sum_const_zero, zero_apply]

theorem derivative_single (φ : R →+* ℝ) (p : MvPolynomial ι R) (x : ι → ℝ) (i : ι) :
    derivative φ p x (Pi.single i 1) = (pderiv i p).eval₂ φ x := by
  classical
  simp [derivative_apply, Pi.single_apply]

theorem critical_iff (φ : R →+* ℝ) (p : MvPolynomial ι R) (x : ι → ℝ) :
    fderiv ℝ (fun y => p.eval₂ φ y) x = 0 ↔ ∀ i, (pderiv i p).eval₂ φ x = 0 := by
  rw [fderiv_eq, linear_eq_zero_iff]
  simp only [derivative_single]

end LeanCanny.Geometry.PolynomialCalculus
