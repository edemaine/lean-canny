/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProduct
public import LeanCanny.Encoding.BinaryNatCode

/-!
# Finite products and omitted factors in complete product trees

Padding with ones lets the uniform tree controller use height equal to a count
word's length. The omitted-factor variant specifies cofactor products directly.
Both statements include empty families and arbitrary binary count words.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct
open scoped BigOperators

def padded (a : ℕ → ℕ) (N i : ℕ) : ℕ := if i < N then a i else 1
def omitted (a : ℕ → ℕ) (N skip i : ℕ) : ℕ := if i < N ∧ i ≠ skip then a i else 1

theorem tree_padded (a : ℕ → ℕ) (N H : ℕ) (hN : N ≤ 2 ^ H) :
    tree (padded a N) H 0 = ∏ i ∈ Finset.range N, a i := by
  rw [tree_eq_prod]
  simp only [Nat.mul_zero, Nat.zero_add]
  symm
  apply Finset.prod_subset_one_on_sdiff (Finset.range_mono hN)
  · intro i hi
    have hn : ¬ i < N := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h)
    simp only [padded, ite_eq_right hn]
  · intro i hi
    simp only [padded, ite_eq_left (Finset.mem_range.mp hi)]

theorem tree_omitted (a : ℕ → ℕ) (N skip H : ℕ) (hN : N ≤ 2 ^ H) :
    tree (omitted a N skip) H 0 = ∏ i ∈ (Finset.range N).erase skip, a i := by
  rw [tree_eq_prod]
  simp only [Nat.mul_zero, Nat.zero_add]
  symm
  have hsub : (Finset.range N).erase skip ⊆ Finset.range (2 ^ H) := by
    intro i hi
    exact Finset.mem_range.mpr ((Finset.mem_range.mp (Finset.mem_erase.mp hi).2).trans_le hN)
  apply Finset.prod_subset_one_on_sdiff hsub
  · intro i hi
    have hn : ¬ (i < N ∧ i ≠ skip) := by
      intro h
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_erase.mpr ⟨h.2, Finset.mem_range.mpr h.1⟩)
    simp only [omitted, ite_eq_right hn]
  · intro i hi
    have he := Finset.mem_erase.mp hi
    have hcond : i < N ∧ i ≠ skip := ⟨Finset.mem_range.mp he.2, he.1⟩
    simp only [omitted, ite_eq_left hcond]

theorem tree_padded_of_bits (a : ℕ → ℕ) (count : List Bool) :
    tree (padded a (Nat.fromBitsLE count)) count.length 0 = ∏ i ∈ Finset.range (Nat.fromBitsLE count), a i :=
  tree_padded a _ _ (Nat.fromBitsLE_lt_pow_length count).le

theorem tree_omitted_of_bits (a : ℕ → ℕ) (count : List Bool) (skip : ℕ) :
    tree (omitted a (Nat.fromBitsLE count) skip) count.length 0 =
      ∏ i ∈ (Finset.range (Nat.fromBitsLE count)).erase skip, a i :=
  tree_omitted a _ _ _ (Nat.fromBitsLE_lt_pow_length count).le

end LeanCanny.Algebra.BalancedProduct
