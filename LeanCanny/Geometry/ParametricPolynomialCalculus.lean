/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Smooth polynomial evaluation with variable coefficients

Polynomial evaluation remains smooth when both the coefficient homomorphism
and the variables depend smoothly on the parameter. The statements cover
univariate and multivariate polynomials at every differentiability order.
-/

@[expose] public section

namespace LeanCanny.Geometry.ParametricPolynomialCalculus

variable {R K E ι : Type*} [CommRing R] [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem polynomial_eval₂ (p : Polynomial R) (φ : E → R →+* K) (x : E → K) (m : WithTop ℕ∞)
    (hφ : ∀ r, ContDiff K m (fun a => φ a r)) (hx : ContDiff K m x) :
    ContDiff K m (fun a => p.eval₂ (φ a) (x a)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial j r => simpa only [Polynomial.eval₂_monomial] using (hφ r).mul (hx.pow j)

theorem mvPolynomial_eval₂ (p : MvPolynomial ι R) (φ : E → R →+* K) (x : E → ι → K) (m : WithTop ℕ∞)
    (hφ : ∀ r, ContDiff K m (fun a => φ a r)) (hx : ∀ i, ContDiff K m (fun a => x a i)) :
    ContDiff K m (fun a => p.eval₂ (φ a) (x a)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval₂_C] using hφ r
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (hx i)

end LeanCanny.Geometry.ParametricPolynomialCalculus
