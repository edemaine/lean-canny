/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSignQueries

/-! # Weighted sign-pattern indicators recover filtered moments

The same integer indicator expansion used for sign counts applies to any
integer-valued weight on the finite root set. In particular, weights may be
products of selected polynomial signs, with negative or cancelling moments.
-/

@[expose] public section
namespace LeanCanny.Algebra.RootSignQueries
open Polynomial
open scoped Classical BigOperators

noncomputable def weightedQuery {J : Type*} [Fintype J] (Z : Finset ℝ)
    (Q : J → ℝ[X]) (e : J → Fin 3) (w : ℝ → ℤ) : ℤ :=
  ∑ x ∈ Z, (∏ i, (SignType.sign ((Q i).eval x) : ℤ) ^ (e i).val) * w x

noncomputable def filteredMoment {J : Type*} (Z : Finset ℝ) (Q : J → ℝ[X])
    (sigma : J → SignType) (w : ℝ → ℤ) : ℤ :=
  ∑ x ∈ Z.filter (fun x => ∀ i, SignType.sign ((Q i).eval x) = sigma i), w x

theorem weighted_queries_eq_moment {J : Type*} [Fintype J] (Z : Finset ℝ)
    (Q : J → ℝ[X]) (sigma : J → SignType) (w : ℝ → ℤ) :
    (∑ e : J → Fin 3, patternWeight sigma e * weightedQuery Z Q e w) =
      2 ^ Fintype.card J * filteredMoment Z Q sigma w := by
  unfold weightedQuery filteredMoment
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, product_indicator, funext_iff, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]

theorem sum_pattern_counts {J : Type*} [Fintype J] (Z : Finset ℝ) (Q : J → ℝ[X])
    (w : (J → SignType) → ℤ) :
    (∑ sigma : J → SignType, w sigma * (signCount Z Q sigma : ℤ)) =
      ∑ x ∈ Z, w (fun i => SignType.sign ((Q i).eval x)) := by
  have h (sigma : J → SignType) : w sigma * (signCount Z Q sigma : ℤ) =
      ∑ x ∈ Z, if (fun i => SignType.sign ((Q i).eval x)) = sigma then w sigma else 0 := by
    simp only [signCount, funext_iff]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm]
    congr 1
    apply congrArg (fun s : Finset ℝ => (s.card : ℤ))
    ext x
    simp only [Finset.mem_filter]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp

end LeanCanny.Algebra.RootSignQueries
