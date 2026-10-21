/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PreprocessedPairCoordinateBounds
public import LeanCanny.Algebra.SeparableIntegerCoordinates

/-! # A common polynomial bound for one primitive-pair stage

For T≥4, input degrees and mass exponents at most T give resultant and pair
coordinate mass exponents at most T^10. The deliberately coarse estimate
supports one uniform bound throughout a balanced tree.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits

theorem sixteen_mul_pow_le (T k : ℕ) (hT : 4 ≤ T) : 16 * T ^ k ≤ T ^ (k + 2) := by
  have hs : 16 ≤ T ^ 2 := by simpa using Nat.pow_le_pow_left hT 2
  calc
    _ ≤ T ^ 2 * T ^ k := Nat.mul_le_mul_right _ hs
    _ = _ := by rw [← pow_add, Nat.add_comm 2 k]

theorem coefficientBudget_uniform (T : ℕ) (hT : 4 ≤ T) : coefficientBudget T T (T ^ 4) T T ≤ T ^ 8 := by
  have hraw : coefficientBudget T T (T ^ 4) T T ≤ T ^ 6 + 9 * T ^ 2 + 3 * T + 1 := by
    unfold coefficientBudget
    calc
      _ ≤ (T + T) * (T + T) + T * ((T + 1) + T + (T + 1) + (T ^ 4 + 1) * T) + T * (T + 1) + 1 := by
        gcongr <;> exact Nat.size_le_self _
      _ = _ := by ring
  have h2 : T ^ 2 ≤ T ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : T ≤ T ^ 6 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 6 by decide)
  have h0 : 1 ≤ T ^ 6 := Nat.one_le_pow _ _ (by omega)
  exact (hraw.trans (by omega : T ^ 6 + 9 * T ^ 2 + 3 * T + 1 ≤ 16 * T ^ 6)).trans (sixteen_mul_pow_le T 6 hT)

theorem coordinateMassBudget_uniform (T : ℕ) (hT : 4 ≤ T) : coordinateMassBudget T T (T ^ 4) T T ≤ T ^ 10 := by
  have hc := coefficientBudget_uniform T hT
  have hraw : coordinateMassBudget T T (T ^ 4) T T ≤ T ^ 8 + T ^ 5 + T ^ 4 + T ^ 2 + 5 * T + 6 := by
    unfold coordinateMassBudget
    calc
      _ ≤ T ^ 8 + ((T + 1) + T + (T + 1) + (T ^ 4 + 1) * T) + (T + 1) + 1 + (T * T + 2) + T ^ 4 := by
        gcongr <;> exact Nat.size_le_self _
      _ = _ := by ring
  have h5 : T ^ 5 ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : T ^ 4 ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : T ^ 2 ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : T ≤ T ^ 8 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 8 by decide)
  have h0 : 1 ≤ T ^ 8 := Nat.one_le_pow _ _ (by omega)
  exact (hraw.trans (by omega : T ^ 8 + T ^ 5 + T ^ 4 + T ^ 2 + 5 * T + 6 ≤ 16 * T ^ 8)).trans (sixteen_mul_pow_le T 8 hT)

theorem resultantMassExponent_uniform (T : ℕ) (hT : 4 ≤ T) : T ^ 8 + (T * T + 1).size ≤ T ^ 10 := by
  have hs := Nat.size_le_self (T * T + 1)
  have h2 : T ^ 2 ≤ T ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h0 : 1 ≤ T ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h : 16 * T ^ 8 ≤ T ^ 10 := sixteen_mul_pow_le T 8 hT
  rw [pow_two] at h2
  omega

end LeanCanny.Algebra.CannyResultantBits
