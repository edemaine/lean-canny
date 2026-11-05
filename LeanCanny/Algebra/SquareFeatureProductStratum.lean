/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeatureProductPositive
/-! # Two coefficient conditions encode the exact number of zero features -/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureProduct
open Polynomial
open scoped Classical

theorem coefficient_zero_iff (a : List ℝ) (k : ℕ) :
    (polynomial a).coeff k = 0 ↔ k < zeroCount a ∨ a.length < k := by
  have HN := coefficient_nonneg a k
  constructor
  · intro H
    have HP : ¬ (zeroCount a ≤ k ∧ k ≤ a.length) := by
      intro h
      have HH := (coefficient_pos_iff a k).mpr h
      rw [H] at HH
      exact lt_irrefl _ HH
    omega
  · intro H
    have HP : ¬ 0 < (polynomial a).coeff k := by
      intro hp
      have HH := (coefficient_pos_iff a k).mp hp
      omega
    exact le_antisymm (le_of_not_gt HP) HN

noncomputable def Lower (a : List ℝ) (k : ℕ) : Prop := k=0 ∨ (polynomial a).coeff (k-1)=0
noncomputable def Certificate (a : List ℝ) (k : ℕ) (w : ℝ) : Prop :=
  Lower a k ∧ (polynomial a).coeff k*w^2=1

theorem lower_positive_iff (a : List ℝ) (k : ℕ) :
    Lower a k ∧ 0 < (polynomial a).coeff k ↔ zeroCount a = k := by
  have HZ := zeroCount_le a
  rw [Lower, coefficient_zero_iff, coefficient_pos_iff]
  omega

theorem exists_certificate_iff (a : List ℝ) (k : ℕ) :
    (∃ w : ℝ, Certificate a k w) ↔ zeroCount a = k := by
  constructor
  · rintro ⟨w,HL,HW⟩
    have HP : 0 < (polynomial a).coeff k := by nlinarith [sq_nonneg w]
    exact (lower_positive_iff a k).mp ⟨HL,HP⟩
  · intro H
    obtain ⟨HL,HP⟩ := (lower_positive_iff a k).mpr H
    refine ⟨(Real.sqrt ((polynomial a).coeff k))⁻¹, HL, ?_⟩
    rw [inv_pow, Real.sq_sqrt HP.le, mul_inv_cancel₀ (ne_of_gt HP)]

noncomputable def equation (a : List ℝ) (k : ℕ) (w : ℝ) : ℝ :=
  (if k=0 then 0 else (polynomial a).coeff (k-1))^2 + ((polynomial a).coeff k*w^2-1)^2

theorem equation_zero_iff (a : List ℝ) (k : ℕ) (w : ℝ) : equation a k w = 0 ↔ Certificate a k w := by
  unfold equation
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _), sq_eq_zero_iff, sq_eq_zero_iff, sub_eq_zero]
  unfold Certificate Lower
  by_cases HK : k=0 <;> simp [HK]

theorem exists_equation_iff (a : List ℝ) (k : ℕ) :
    (∃ w : ℝ, equation a k w = 0) ↔ zeroCount a = k := by
  simp_rw [equation_zero_iff]
  exact exists_certificate_iff a k

theorem no_equation_above_count (a : List ℝ) (k : ℕ) (hk : a.length < k) :
    ¬ ∃ w : ℝ, equation a k w = 0 := by
  rw [exists_equation_iff]
  have H := zeroCount_le a
  omega

end LeanCanny.Algebra.SquareFeatureProduct
