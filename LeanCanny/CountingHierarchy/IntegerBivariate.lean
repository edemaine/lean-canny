/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Integer bivariate evaluation and swapping -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial

/-- Swapping the variables commutes with evaluation over a commutative ring. -/
theorem integer_bivariate_swap_eval {K : Type*} [CommRing K]
    (P : Polynomial (Polynomial ℤ)) (x y : K) :
    (Bivariate.swap P).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom K) x) y =
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom K) y) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | monomial k a =>
    simp only [Bivariate.swap_monomial, eval₂_mul, eval₂_map, eval₂_C, eval₂_pow,
      eval₂_X, eval₂_monomial, Polynomial.coe_eval₂RingHom]
    congr 1
    simp only [Polynomial.eval₂RingHom_comp_C]

/-- The constant coefficient after swapping is evaluation of the original
 parameter at zero, coefficient by coefficient. -/
theorem integer_bivariate_swap_coeff_zero (P : Polynomial (Polynomial ℤ)) :
    (Bivariate.swap P).coeff 0 = P.map (Polynomial.evalRingHom 0) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, Polynomial.map_add]
  | monomial k a =>
    simp only [Bivariate.swap_monomial, mul_coeff_zero, coeff_map, coeff_C,
      map_monomial]
    rw [← C_mul_X_pow_eq_monomial]
    change C (a.coeff 0) * X ^ k = C (a.eval 0) * X ^ k
    rw [← Polynomial.coeff_zero_eq_eval_zero]

end LeanCanny.CountingHierarchy
