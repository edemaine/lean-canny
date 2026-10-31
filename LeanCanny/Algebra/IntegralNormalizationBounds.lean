/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedDegreeIntegralNormalization
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Binary height bounds for fixed-degree integral normalization

Normalization multiplies a coefficient-height exponent by the selected
degree. Both may be binary values; their product still has an FP reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedDegreeIntegralNormalization
open Polynomial
open scoped Classical

theorem coefficient_natAbs_le (p : Polynomial ℤ) (d B : ℕ) (hB : 1 ≤ B)
    (hp : ∀ k, (p.coeff k).natAbs ≤ B) (k : ℕ) :
    ((polynomial p d).coeff k).natAbs ≤ B ^ d := by
  by_cases he : k = d
  · subst k
    rw [coefficient_top, Int.natAbs_one]
    exact one_le_pow₀ hB
  · rw [coefficient, ite_eq_right he, zero_add]
    by_cases hk : k < d
    · rw [ite_eq_left hk, Int.natAbs_mul, Int.natAbs_pow]
      calc
        _ ≤ B * B ^ (d - 1 - k) := Nat.mul_le_mul (hp k) (Nat.pow_le_pow_left (hp d) _)
        _ = B ^ (d - 1 - k + 1) := (pow_succ' _ _).symm
        _ ≤ B ^ d := Nat.pow_le_pow_right hB (by omega)
    · rw [ite_eq_right hk, Int.natAbs_zero]
      exact Nat.zero_le _

theorem coefficient_height_le (p : Polynomial ℤ) (d h : ℕ)
    (hp : ∀ k, (p.coeff k).natAbs ≤ 2 ^ h) (k : ℕ) :
    ((polynomial p d).coeff k).natAbs ≤ 2 ^ (h * d) := by
  simpa only [← pow_mul] using coefficient_natAbs_le p d (2 ^ h) (Nat.one_le_two_pow) hp k

theorem coefficient_bits_le (p : Polynomial ℤ) (d h : ℕ)
    (hp : ∀ k, (p.coeff k).natAbs ≤ 2 ^ h) (k : ℕ) :
    ((polynomial p d).coeff k).natAbs.size ≤ h * d + 1 := by
  have H := Nat.size_le_size (coefficient_height_le p d h hp k)
  simpa only [Nat.size_pow] using H

theorem height_binary {h d : List Bool → ℕ} (hh : BinaryFn h) (hd : BinaryFn d) :
    BinaryFn (fun c => h c * d c) := hh.mul hd

theorem bits_binary {h d : List Bool → ℕ} (hh : BinaryFn h) (hd : BinaryFn d) :
    BinaryFn (fun c => h c * d c + 1) := (hh.mul hd).add (BinaryFn.const 1)

end LeanCanny.Algebra.FixedDegreeIntegralNormalization
