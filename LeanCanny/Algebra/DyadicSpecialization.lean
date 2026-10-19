/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.EffectiveInfinitesimalSign
import Mathlib.Tactic.Ring

/-! # Integral dyadic specialization with a fixed denominator-clearing degree

The integer sum represents 2^(s*D) times evaluation at beta=2^(-s).
Neither the denominator nor this integer needs to be materialized by the
coefficient-access implementation. Coefficient mass gives a binary bit budget.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicSpecialization
open Polynomial
open scoped BigOperators

def numerator (p : ℤ[X]) (D s : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (D + 1), p.coeff i * (2 : ℤ) ^ (s * (D - i))

@[simp] theorem numerator_zero (D s : ℕ) : numerator 0 D s = 0 := by simp [numerator]

theorem numerator_eval (p : ℤ[X]) (D s : ℕ) (hD : p.natDegree ≤ D) :
    (numerator p D s : ℝ) = (2 : ℝ) ^ (s * D) *
      p.eval₂ (Int.castRingHom ℝ) (InfinitesimalSign.dyadic s) := by
  rw [numerator, Int.cast_sum, Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℝ) (n := D + 1) (by omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiD : i ≤ D := by have := Finset.mem_range.mp hi; omega
  have he : (2 : ℝ) ^ (s * D) * InfinitesimalSign.dyadic s ^ i = (2 : ℝ) ^ (s * (D - i)) := by
    simp only [InfinitesimalSign.dyadic, pow_mul, inv_pow]
    rw [pow_sub₀ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hiD]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.coe_castRingHom]
  rw [← he]
  ring

theorem numerator_abs_le (p : ℤ[X]) (D s : ℕ) (hD : p.natDegree ≤ D) :
    (numerator p D s).natAbs ≤ coefficientMass p * 2 ^ (s * D) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (D + 1), (p.coeff i * (2 : ℤ) ^ (s * (D - i))).natAbs :=
      Int.natAbs_sum_le _ _
    _ = ∑ i ∈ Finset.range (D + 1), (p.coeff i).natAbs * 2 ^ (s * (D - i)) := by
      simp only [Int.natAbs_mul, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
    _ ≤ ∑ i ∈ Finset.range (D + 1), (p.coeff i).natAbs * 2 ^ (s * D) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_left s (Nat.sub_le D i)))
    _ = coefficientMass p * 2 ^ (s * D) := by
      rw [← Finset.sum_mul, coefficientMass, p.sum_over_range' (fun _ => rfl) (D + 1) (by omega)]

theorem numerator_size_le (p : ℤ[X]) (D s b : ℕ) (hD : p.natDegree ≤ D)
    (hm : coefficientMass p ≤ 2 ^ b) : (numerator p D s).natAbs.size ≤ b + s * D + 1 := by
  have h := (numerator_abs_le p D s hD).trans (Nat.mul_le_mul_right _ hm)
  rw [← pow_add] at h
  simpa only [Nat.size_pow] using Nat.size_le_size h

theorem numerator_sign (p : ℤ[X]) (D s b : ℕ) (hD : p.natDegree ≤ D)
    (hm : coefficientMass p ≤ 2 ^ b) (hs : b < s) :
    SignType.sign (numerator p D s) = SignType.sign p.trailingCoeff := by
  have hc : SignType.sign ((numerator p D s : ℤ) : ℝ) = SignType.sign (numerator p D s) := sign_intCast _
  rw [← hc, numerator_eval p D s hD, sign_mul, sign_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _), one_mul]
  exact InfinitesimalSign.integer_sign_eval_dyadic p b s hm hs

end LeanCanny.Algebra.DyadicSpecialization
