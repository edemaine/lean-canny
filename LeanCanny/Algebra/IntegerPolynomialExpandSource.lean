/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import Mathlib.Algebra.Polynomial.Expand

/-! # Power substitution in integer root sources

Only the scalar root variable is expanded. This construction neither
serializes the polynomial nor changes an original spatial LOW source.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialExpandSource
open Polynomial
open scoped BigOperators Classical

theorem mass_le (p : Polynomial ℤ) (d : ℕ) : coefficientMass (Polynomial.expand ℤ d p)≤coefficientMass p := by
  conv_lhs=>rw [←Polynomial.sum_monomial_eq p]
  simp only [Polynomial.sum_def,map_sum,Polynomial.expand_monomial]
  exact (coefficientMass_sum_le _ _).trans_eq (by simp only [coefficientMass_monomial]; rfl)

noncomputable def source (S : IntegerPolynomialRootQueriesBits.Source) (d : List Bool→ℕ) :
    IntegerPolynomialRootQueriesBits.Source where
  polynomial q:=Polynomial.expand ℤ (d q) (S.polynomial q)
  degree q:=S.degree q*d q
  mass:=S.mass
  degree_bound q:=by rw [Polynomial.natDegree_expand]; exact Nat.mul_le_mul_right _ (S.degree_bound q)
  mass_bound q:=(mass_le _ _).trans (S.mass_bound q)

theorem eval (S : IntegerPolynomialRootQueriesBits.Source) (d : List Bool→ℕ) (q : List Bool) (a : ℝ) :
    ((source S d).polynomial q).eval₂ (Int.castRingHom ℝ) a=
      (S.polynomial q).eval₂ (Int.castRingHom ℝ) (a^d q) := by
  simp only [source,Polynomial.expand_eq_comp_X_pow,Polynomial.eval₂_comp,Polynomial.eval₂_X_pow]

end LeanCanny.Algebra.IntegerPolynomialExpandSource
