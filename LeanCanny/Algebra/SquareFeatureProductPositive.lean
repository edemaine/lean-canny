/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientMass
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
/-! # No gaps in the nonnegative coefficients of squared-feature products -/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureProduct
open Polynomial
open scoped Classical

noncomputable def polynomial (a : List ℝ) : ℝ[X] := (a.map (fun x => X + C (x^2))).prod
noncomputable def zeroCount (a : List ℝ) := (a.filter (fun x => decide (x=0))).length

theorem zeroCount_le (a : List ℝ) : zeroCount a ≤ a.length := List.length_filter_le _ _
theorem zeroCount_cons (x : ℝ) (a : List ℝ) :
    zeroCount (x::a) = if x=0 then zeroCount a+1 else zeroCount a := by
  by_cases hx : x=0 <;> simp [zeroCount, hx]
private theorem polynomial_cons (x : ℝ) (a : List ℝ) :
    polynomial (x::a) = (X+C (x^2))*polynomial a := by simp [polynomial]
private theorem coeff_zero (x : ℝ) (a : List ℝ) :
    (polynomial (x::a)).coeff 0 = x^2*(polynomial a).coeff 0 := by
  rw [polynomial_cons, add_mul, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]
private theorem coeff_succ (x : ℝ) (a : List ℝ) (k : ℕ) :
    (polynomial (x::a)).coeff (k+1) = (polynomial a).coeff k+x^2*(polynomial a).coeff (k+1) := by
  rw [polynomial_cons, add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

theorem coefficient_nonneg (a : List ℝ) (k : ℕ) : 0 ≤ (polynomial a).coeff k := by
  induction a generalizing k with
  | nil => by_cases hk : k=0 <;> simp [polynomial, coeff_one, hk]
  | cons x a ih =>
      cases k with
      | zero => rw [coeff_zero]; exact mul_nonneg (sq_nonneg _) (ih 0)
      | succ k => rw [coeff_succ]; exact add_nonneg (ih k) (mul_nonneg (sq_nonneg _) (ih (k+1)))

private theorem add_positive (a b : ℝ) (ha : 0≤a) (hb : 0≤b) : 0<a+b ↔ 0<a ∨ 0<b := by
  constructor
  · intro h
    by_cases hA : 0<a
    · exact Or.inl hA
    · exact Or.inr (by linarith)
  · rintro (h|h) <;> linarith

/-- Every coefficient between the number of zero features and the full
factor count is strictly positive; there are no intermediate gaps. -/
theorem coefficient_pos_iff (a : List ℝ) (k : ℕ) :
    0 < (polynomial a).coeff k ↔ zeroCount a ≤ k ∧ k ≤ a.length := by
  induction a generalizing k with
  | nil =>
      by_cases hk : k=0
      · subst k; simp [polynomial, zeroCount]
      · simp [polynomial, zeroCount, coeff_one, hk]
  | cons x a ih =>
      have HZ := zeroCount_le a
      rw [zeroCount_cons, List.length_cons]
      by_cases hx : x=0
      · rw [ite_eq_left hx]
        cases k with
        | zero => simp [coeff_zero, hx]
        | succ k =>
            simp only [coeff_succ, hx, zero_pow (by decide : 2≠0), zero_mul, add_zero]
            rw [ih k]
            omega
      · rw [ite_eq_right hx]
        have HP : 0<x^2 := sq_pos_of_ne_zero hx
        cases k with
        | zero => rw [coeff_zero, mul_pos_iff_of_pos_left HP, ih 0]; omega
        | succ k =>
            rw [coeff_succ, add_positive _ _ (coefficient_nonneg _ _)
              (mul_nonneg HP.le (coefficient_nonneg _ _)), mul_pos_iff_of_pos_left HP, ih k, ih (k+1)]
            omega

end LeanCanny.Algebra.SquareFeatureProduct
