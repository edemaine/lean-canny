/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.TernaryFP

/-! # Native ternary words with every exponent equal to one

The integer `3^k / 2` has exactly k ternary digits equal to one. A unary
bound on k permits a polynomial-time binary writer, including k = 0.
-/

@[expose] public section
namespace LeanCanny.Encoding.Ternary

theorem half_power_succ (k : ℕ) : 3 ^ (k + 1) / 2 = 3 * (3 ^ k / 2) + 1 := by
  have hm : 3 ^ k % 2 = 1 := by simp [Nat.pow_mod]
  have he := Nat.mod_add_div (3 ^ k) 2
  rw [hm] at he
  rw [pow_succ, ← he]
  omega

theorem half_power_digit (k i : ℕ) (hi : i < k) : (3 ^ k / 2 / 3 ^ i) % 3 = 1 := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero =>
      rw [half_power_succ]
      omega
    | succ i =>
      have hs : 3 ^ (k + 1) / 2 / 3 = 3 ^ k / 2 := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm 2 3, ← Nat.div_div_eq_div_mul,
          pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 3)]
      rw [show 3 ^ (i + 1) = 3 * 3 ^ i from pow_succ' _ _, ← Nat.div_div_eq_div_mul, hs]
      exact ih i (by omega)

theorem exponent_ones (k i : ℕ) (hi : i < k) : exponent k (3 ^ k / 2) i = 1 := by
  apply Fin.ext
  simp only [exponent, hi, ite_true]
  exact half_power_digit k i hi

def ones (k : List Bool) : List Bool := BinaryNat.div (pair (count k) (BinaryNatCode.encode 2))

theorem ones_eq (k : List Bool) : ones k = BinaryNatCode.encode (3 ^ Nat.fromBitsLE k / 2) := by
  simp only [ones, count_eq, BinaryNat.div_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem ones_FP {k : List Bool → List Bool} (hk : k ∈ FP)
    (hu : UnaryFn (fun c => Nat.fromBitsLE (k c))) : (fun c => ones (k c)) ∈ FP :=
  mem_FP_comp (mem_FP_pair (count_mem_FP hk hu) (constFn_mem_FP _)) BinaryNat.div_mem_FP

end LeanCanny.Encoding.Ternary
