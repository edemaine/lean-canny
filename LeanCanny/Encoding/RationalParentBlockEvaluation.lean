/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentBlockCodes

/-! # Exact coordinate-block evaluation over rational parents -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentBlockCodes
open LeanCanny.Algebra LeanCanny.ETR RationalCoordinateFamily
open BoundedCriticalSampleBlockSource (InBlock environment environment_zero environment_variable)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def assignment (A : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (y : Fin (dim u) → ℝ) (i : ℕ) : ℝ :=
  if hi : InBlock (offset u) (dim u) i then y ⟨i - offset u, by unfold InBlock at hi; omega⟩
  else point A u theta i

theorem denominator_nonzero (A : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hA : Defined A u theta) (y : Fin (dim u) → ℝ) (i : ℕ) :
    (coordinate A offset dim false u i).eval₂ (Int.castRingHom ℝ) (environment _ theta y) ≠ 0 := by
  simp only [coordinate, Bool.false_eq_true, ite_false]
  split_ifs
  · simp only [MvPolynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]
  · rw [IndexedMultivariateRational.eval_parameter, environment_zero]
    exact hA i

theorem denominator_constant (A : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (y z : Fin (dim u) → ℝ) (i : ℕ) :
    (coordinate A offset dim false u i).eval₂ (Int.castRingHom ℝ) (environment _ theta y) =
      (coordinate A offset dim false u i).eval₂ (Int.castRingHom ℝ) (environment _ theta z) := by
  simp only [coordinate, Bool.false_eq_true, ite_false]
  split_ifs
  · simp only [MvPolynomial.eval₂_one]
  · simp only [IndexedMultivariateRational.eval_parameter, environment_zero]

theorem coordinate_eval (A : Family) (offset dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (y : Fin (dim u) → ℝ) (i : ℕ) :
    (coordinate A offset dim true u i).eval₂ (Int.castRingHom ℝ) (environment _ theta y) /
      (coordinate A offset dim false u i).eval₂ (Int.castRingHom ℝ) (environment _ theta y) =
        assignment A offset dim u theta y i := by
  simp only [coordinate, assignment, Bool.false_eq_true, ite_false, ite_true]
  split_ifs
  · rw [MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, div_one, environment_variable]
  · simp only [IndexedMultivariateRational.eval_parameter, environment_zero]
    rfl

end LeanCanny.Encoding.RationalParentBlockCodes
