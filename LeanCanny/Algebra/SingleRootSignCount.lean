/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSignQueries

/-! # Distinct-root counts from three scalar Tarski moments

The unit query counts distinct roots. The first two sign moments distinguish
zero, positive, and negative query values. The zero head uses the empty root
list convention throughout.
-/

@[expose] public section
namespace LeanCanny.Algebra.RootSignQueries
open Polynomial
open scoped Classical BigOperators

noncomputable def singleSignCount (p q : ℝ[X]) (s : SignType) : ℕ :=
  (p.roots.toFinset.filter (fun x => SignType.sign (q.eval x) = s)).card

theorem singleSignCount_sum (p q : ℝ[X]) (s : SignType) :
    (singleSignCount p q s : ℤ) = ∑ x ∈ p.roots.toFinset, if SignType.sign (q.eval x) = s then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp only [singleSignCount, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem tarskiQuery_one (p : ℝ[X]) : tarskiQuery p 1 = (p.roots.toFinset.card : ℤ) := by
  simp [tarskiQuery, signSum]

theorem sign_square_eval (q : ℝ[X]) (x : ℝ) :
    (SignType.sign ((q ^ 2).eval x) : ℤ) = (SignType.sign (q.eval x) : ℤ) ^ 2 := by
  let φ : ℝ →*₀ ℤ := SignType.castHom.comp signHom
  change φ ((q ^ 2).eval x) = φ (q.eval x) ^ 2
  rw [Polynomial.eval_pow, map_pow]

theorem singleSignCount_zero (p q : ℝ[X]) :
    (singleSignCount p q 0 : ℤ) = tarskiQuery p 1 - tarskiQuery p (q ^ 2) := by
  rw [singleSignCount_sum]
  simp only [tarskiQuery, signSum, Polynomial.eval_one, sign_one, SignType.coe_one,
    ← Finset.sum_sub_distrib, sign_square_eval]
  apply Finset.sum_congr rfl
  intro x _
  cases h : SignType.sign (q.eval x) <;> norm_num

theorem singleSignCount_positive (p q : ℝ[X]) :
    2 * (singleSignCount p q .pos : ℤ) = tarskiQuery p (q ^ 2) + tarskiQuery p q := by
  rw [singleSignCount_sum, Finset.mul_sum]
  simp only [tarskiQuery, signSum, ← Finset.sum_add_distrib, sign_square_eval]
  apply Finset.sum_congr rfl
  intro x _
  cases h : SignType.sign (q.eval x) <;> norm_num

theorem singleSignCount_negative (p q : ℝ[X]) :
    2 * (singleSignCount p q .neg : ℤ) = tarskiQuery p (q ^ 2) - tarskiQuery p q := by
  rw [singleSignCount_sum, Finset.mul_sum]
  simp only [tarskiQuery, signSum, ← Finset.sum_sub_distrib, sign_square_eval]
  apply Finset.sum_congr rfl
  intro x _
  cases h : SignType.sign (q.eval x) <;> norm_num

end LeanCanny.Algebra.RootSignQueries
