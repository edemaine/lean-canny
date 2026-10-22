/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGridAvoidance
public import Mathlib.Tactic.LinearCombination

/-! # Bounded integer choices avoiding affine equations

A family of m nonzero affine forms admits a common nonzero evaluation with
integer coordinates between zero and m. This specializes polynomial grid
avoidance to the projection conditions used in coordinate recovery.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineGridAvoidance
open MvPolynomial
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K]

noncomputable def polynomial (a : ι → K) (b : K) : MvPolynomial ι K :=
  C b + ∑ i, C (a i) * X i

theorem eval_polynomial (a : ι → K) (b : K) (c : ι → K) :
    eval c (polynomial a b) = b + ∑ i, a i * c i := by
  simp [polynomial]

theorem totalDegree_polynomial (a : ι → K) (b : K) :
    (polynomial a b).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp)

theorem polynomial_ne_zero (a : ι → K) (b : K) (h : (∃ i, a i ≠ 0) ∨ b ≠ 0) :
    polynomial a b ≠ 0 := by
  classical
  intro hz
  have hb : b = 0 := by
    have he := congrArg (eval (fun _ : ι => (0 : K))) hz
    rw [eval_polynomial] at he
    simpa using he
  rcases h with ⟨i, hi⟩ | hb'
  · apply hi
    have he := congrArg (eval (Pi.single i (1 : K))) hz
    simpa [eval_polynomial, hb, Pi.single_apply, mul_ite] using he
  · exact hb' hb

theorem exists_bounded_nat [CharZero K] {σ : Type*} [Fintype σ]
    (a : σ → ι → K) (b : σ → K) (h : ∀ j, (∃ i, a j i ≠ 0) ∨ b j ≠ 0) :
    ∃ c : ι → ℕ, (∀ i, c i ≤ Fintype.card σ) ∧ ∀ j, b j + ∑ i, a j i * (c i : K) ≠ 0 := by
  classical
  obtain ⟨c, hc, he⟩ := PolynomialGridAvoidance.exists_nat_common_nonzero
    (fun j => polynomial (a j) (b j)) (fun j => polynomial_ne_zero _ _ (h j))
    (Fintype.card σ) (by
      calc
        ∑ j, (polynomial (a j) (b j)).totalDegree ≤ ∑ _j : σ, 1 :=
          Finset.sum_le_sum (fun j _ => totalDegree_polynomial _ _)
        _ = Fintype.card σ := by simp)
  exact ⟨c, hc, fun j => by simpa only [eval_polynomial] using he j⟩

/-- Simultaneously separate finite families of distinct vectors, allowing an
arbitrary affine offset on each vector. -/
theorem exists_bounded_separating_direction [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (a : σ → τ → ι → K) (b : σ → τ → K) (ha : ∀ r, Function.Injective (a r)) :
    ∃ c : ι → ℕ, (∀ i, c i ≤ Fintype.card σ * Fintype.card τ ^ 2) ∧
      ∀ r, Function.Injective (fun p => b r p + ∑ i, a r p i * (c i : K)) := by
  classical
  let coeff : (σ × τ × τ) → ι → K := fun j i =>
    if j.2.1 = j.2.2 then 0 else a j.1 j.2.1 i - a j.1 j.2.2 i
  let offset : (σ × τ × τ) → K := fun j =>
    if j.2.1 = j.2.2 then 1 else b j.1 j.2.1 - b j.1 j.2.2
  have hnonzero (j : σ × τ × τ) : (∃ i, coeff j i ≠ 0) ∨ offset j ≠ 0 := by
    by_cases he : j.2.1 = j.2.2
    · exact Or.inr (by simp [offset, he])
    · left
      by_contra hn
      apply he
      apply ha j.1
      funext i
      by_contra hi
      exact hn ⟨i, by simpa [coeff, he] using sub_ne_zero.mpr hi⟩
  obtain ⟨c, hc, he⟩ := exists_bounded_nat coeff offset hnonzero
  refine ⟨c, fun i => by simpa [Fintype.card_prod, pow_two, mul_assoc] using hc i, ?_⟩
  intro r p q hpq
  by_contra hn
  have hne := he (r, p, q)
  apply hne
  simp only [coeff, offset, ite_eq_right hn]
  simp only [sub_mul, Finset.sum_sub_distrib]
  linear_combination hpq

end LeanCanny.Algebra.AffineGridAvoidance
