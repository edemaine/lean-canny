/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Coefficients and degree after swapping polynomial variables -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial

variable {R : Type*} [CommRing R]

theorem bivariate_swap_coeff (P : Polynomial (Polynomial R)) (i j : ℕ) :
    ((Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial k a =>
    induction a using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
    | monomial l c =>
      by_cases hki : k = j <;> by_cases hli : l = i <;>
        simp [Bivariate.swap_monomial_monomial, Polynomial.coeff_monomial, hki, hli]

theorem bivariate_swap_coefficient_degree_le (P : Polynomial (Polynomial R)) (i : ℕ) :
    ((Bivariate.swap P).coeff i).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [bivariate_swap_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hj, Polynomial.coeff_zero]

theorem bivariate_swap_degree_le (P : Polynomial (Polynomial R)) (H : ℕ)
    (hH : ∀ j, (P.coeff j).natDegree ≤ H) : (Bivariate.swap P).natDegree ≤ H := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply Polynomial.ext
  intro j
  rw [bivariate_swap_coeff, Polynomial.coeff_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hH j).trans_lt hi)

theorem bivariate_swap_eval (P : Polynomial (Polynomial R)) (x y : R) :
    (Bivariate.swap P).eval₂ (Polynomial.evalRingHom x) y =
      P.eval₂ (Polynomial.evalRingHom y) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | monomial k a =>
    simp only [Bivariate.swap_monomial, eval₂_mul, eval₂_map, eval₂_C, eval₂_monomial, Polynomial.coe_evalRingHom]
    congr 1
    · have hcomp : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id R := by
        ext r
        exact Polynomial.eval_C
      rw [hcomp, Polynomial.eval₂_id]
    · simp only [Polynomial.eval_pow, Polynomial.eval_X]

end LeanCanny.CountingHierarchy
