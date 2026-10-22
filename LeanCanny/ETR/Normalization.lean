/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Syntax
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

/-!
# Algebraic normalization steps for ETR

The lemmas below eliminate a single strict inequality or disequality using one fresh real
variable. They also combine two equations into a single equation for conjunction or
disjunction. These are semantic equivalences; the polynomial-time compilation of arbitrary
encoded Boolean formulas is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.ETR

/-- A nonzero real number has a multiplicative inverse, and conversely. -/
theorem ne_zero_iff_exists_mul_eq_one (x : ℝ) :
    x ≠ 0 ↔ ∃ y : ℝ, x * y = 1 := by
  constructor
  · intro hx
    exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩
  · rintro ⟨y, hy⟩ hx
    simp [hx] at hy

/-- A strict negative sign is witnessed by the equation `x*y² + 1 = 0`. -/
theorem lt_zero_iff_exists_mul_sq_add_one_eq_zero (x : ℝ) :
    x < 0 ↔ ∃ y : ℝ, x * (y * y) + 1 = 0 := by
  constructor
  · intro hx
    have hx0 : x ≠ 0 := ne_of_lt hx
    refine ⟨Real.sqrt (-x⁻¹), ?_⟩
    have hnonneg : 0 ≤ -x⁻¹ := neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt hx))
    rw [← pow_two, Real.sq_sqrt hnonneg, mul_neg, mul_inv_cancel₀ hx0]
    norm_num
  · rintro ⟨y, hy⟩
    have hs : 0 ≤ y * y := mul_self_nonneg y
    by_contra h
    have hx : 0 ≤ x := le_of_not_gt h
    have := mul_nonneg hx hs
    linarith

/-- A weak negative sign is witnessed by the equation `x + y² = 0`. -/
theorem le_zero_iff_exists_add_sq_eq_zero (x : ℝ) :
    x ≤ 0 ↔ ∃ y : ℝ, x + y * y = 0 := by
  constructor
  · intro hx
    refine ⟨Real.sqrt (-x), ?_⟩
    rw [← pow_two, Real.sq_sqrt (neg_nonneg.mpr hx)]
    exact add_neg_cancel x
  · rintro ⟨y, hy⟩
    have := mul_self_nonneg y
    linarith

/-- Conjunction of real equations is a sum-of-squares equation. -/
theorem sq_add_sq_eq_zero_iff (x y : ℝ) :
    x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
  mul_self_add_mul_self_eq_zero

namespace Term

/-- `t²`, using the existing expression-tree operations. -/
def square (t : Term) : Term := .mul t t

/-- The equation expressing that `t` is nonzero, with witness variable `i`. -/
def nonzeroEquation (t : Term) (i : ℕ) : Term := .add (.mul t (.var i)) (.const (-1))

/-- The equation expressing that `t < 0`, with witness variable `i`. -/
def negativeEquation (t : Term) (i : ℕ) : Term :=
  .add (.mul t (.square (.var i))) (.const 1)

/-- Changing an assignment at a fresh index does not change a term's value. -/
theorem eval_update_fresh (t : Term) (env : ℕ → ℝ) (i : ℕ) (y : ℝ)
    (hi : t.arity ≤ i) : t.eval (Function.update env i y) = t.eval env := by
  apply t.eval_congr
  intro j hj
  exact Function.update_of_ne (by omega : j ≠ i) y env

end Term

namespace Formula

/-- Existentially quantify one fresh variable to eliminate a disequality. -/
theorem satisfiable_not_eqZero_iff (t : Term) :
    (not (eqZero t)).Satisfiable ↔ (eqZero (t.nonzeroEquation t.arity)).Satisfiable := by
  constructor
  · rintro ⟨env, h⟩
    obtain ⟨y, hy⟩ := (ne_zero_iff_exists_mul_eq_one (t.eval env)).mp h
    refine ⟨Function.update env t.arity y, ?_⟩
    simp only [Holds, Term.nonzeroEquation, Term.eval, Term.eval_update_fresh t env _ y le_rfl,
      Function.update_self, Int.cast_neg, Int.cast_one]
    linarith
  · rintro ⟨env, h⟩
    refine ⟨env, ?_⟩
    change ¬ t.eval env = 0
    simp only [Holds, Term.nonzeroEquation, Term.eval, Int.cast_neg, Int.cast_one] at h
    apply (ne_zero_iff_exists_mul_eq_one _).mpr
    exact ⟨env t.arity, by linarith⟩

/-- Existentially quantify one fresh variable to eliminate a strict inequality. -/
theorem satisfiable_ltZero_iff (t : Term) :
    (ltZero t).Satisfiable ↔ (eqZero (t.negativeEquation t.arity)).Satisfiable := by
  constructor
  · rintro ⟨env, h⟩
    obtain ⟨y, hy⟩ := (lt_zero_iff_exists_mul_sq_add_one_eq_zero (t.eval env)).mp h
    refine ⟨Function.update env t.arity y, ?_⟩
    simpa only [Holds, Term.negativeEquation, Term.square, Term.eval,
      Term.eval_update_fresh t env _ y le_rfl, Function.update_self, Int.cast_one] using hy
  · rintro ⟨env, h⟩
    refine ⟨env, (lt_zero_iff_exists_mul_sq_add_one_eq_zero _).mpr ⟨env t.arity, ?_⟩⟩
    simpa only [Holds, Term.negativeEquation, Term.square, Term.eval, Int.cast_one] using h

/-- Combine two equality atoms into one equation, under the same assignment. -/
theorem holds_and_eqZero_iff (a b : Term) (env : ℕ → ℝ) :
    (and (eqZero a) (eqZero b)).Holds env ↔
      (eqZero (.add a.square b.square)).Holds env :=
  (sq_add_sq_eq_zero_iff _ _).symm

/-- Disjunction of equality atoms is the zero set of their product. -/
theorem holds_or_eqZero_iff (a b : Term) (env : ℕ → ℝ) :
    (or (eqZero a) (eqZero b)).Holds env ↔ (eqZero (.mul a b)).Holds env :=
  mul_eq_zero.symm

end Formula
end LeanCanny.ETR
