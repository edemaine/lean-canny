/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Size

/-! # A common dyadic grid isolates a quantitatively separated finite set -/

@[expose] public section
namespace LeanCanny.Algebra.DyadicIsolatingInterval
open scoped Classical

def lower (k : ℤ) (n : ℕ) : ℚ := (k : ℚ) / 2 ^ n
def upper (k : ℤ) (n : ℕ) : ℚ := ((k + 1 : ℤ) : ℚ) / 2 ^ n

theorem lower_cast (k : ℤ) (n : ℕ) : (lower k n : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by simp [lower]
theorem upper_cast (k : ℤ) (n : ℕ) : (upper k n : ℝ) = ((k : ℝ) + 1) / (2 : ℝ) ^ n := by simp [upper]

theorem width (k : ℤ) (n : ℕ) : (upper k n : ℝ) - (lower k n : ℝ) = ((2 : ℝ) ^ n)⁻¹ := by
  rw [lower_cast, upper_cast]
  ring

theorem exists_index (x : ℝ) (n : ℕ) : ∃ k : ℤ, (lower k n : ℝ) ≤ x ∧ x < (upper k n : ℝ) := by
  have hp : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  refine ⟨⌊x * (2 : ℝ) ^ n⌋, ?_, ?_⟩
  · rw [lower_cast, div_le_iff₀ hp]
    exact Int.floor_le _
  · rw [upper_cast, lt_div_iff₀ hp]
    exact Int.lt_floor_add_one _

theorem index_size (k : ℤ) (n R : ℕ) (x : ℝ) (hl : (lower k n : ℝ) ≤ x)
    (hu : x < (upper k n : ℝ)) (hx : |x| < (2 : ℝ) ^ R) : k.natAbs.size ≤ n + R + 1 := by
  have hp : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
  rw [lower_cast, div_le_iff₀ hp] at hl
  rw [upper_cast, lt_div_iff₀ hp] at hu
  obtain ⟨hxneg, hxpos⟩ := abs_lt.mp hx
  have hpos := mul_lt_mul_of_pos_right hxpos hp
  have hneg := mul_lt_mul_of_pos_right hxneg hp
  rw [← pow_add] at hpos
  rw [neg_mul, ← pow_add] at hneg
  have habs : |(k : ℝ)| < (2 : ℝ) ^ (R + n) + 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hreal : (k.natAbs : ℝ) < (2 : ℝ) ^ (R + n) + 1 := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habs
  have hnat : k.natAbs < 2 ^ (R + n) + 1 := by exact_mod_cast hreal
  have hpow : k.natAbs < 2 ^ (R + n + 1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := R + n)
    omega
  have := Nat.size_le.mpr hpow
  omega

theorem isolates (s : Finset ℝ) (n : ℕ)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ((2 : ℝ) ^ n)⁻¹ < |a - b|)
    (x : ℝ) (hx : x ∈ s) : ∃ k : ℤ,
      (lower k n : ℝ) ≤ x ∧ x < (upper k n : ℝ) ∧
      s.filter (fun y => y < (lower k n : ℝ)) = s.filter (fun y => y < x) ∧
      s.filter (fun y => y < (upper k n : ℝ)) = insert x (s.filter (fun y => y < x)) := by
  obtain ⟨k, hl, hu⟩ := exists_index x n
  have hw := width k n
  refine ⟨k, hl, hu, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hyl⟩
      exact ⟨hy, hyl.trans_le hl⟩
    · rintro ⟨hy, hyx⟩
      refine ⟨hy, ?_⟩
      by_contra hn
      have hly := le_of_not_gt hn
      have hg := hsep y hy x hx (ne_of_lt hyx)
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hyx)] at hg
      linarith
  · ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hy, hyu⟩
      by_cases he : y = x
      · exact Or.inl he
      · right
        refine ⟨hy, ?_⟩
        by_contra hn
        have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
        have hg := hsep y hy x hx he
        rw [abs_of_pos (sub_pos.mpr hxy)] at hg
        linarith
    · rintro (rfl | ⟨hy, hyx⟩)
      · exact ⟨hx, hu⟩
      · exact ⟨hy, hyx.trans hu⟩

end LeanCanny.Algebra.DyadicIsolatingInterval
