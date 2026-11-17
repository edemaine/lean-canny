/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Elementary separation of roots of unity

The vanishing geometric sum gives a separation estimate without angles:
compare its terms with one, and bound each power difference by telescoping.
-/

public section

namespace LeanCanny.CountingHierarchy

open scoped BigOperators

private theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖z ^ k - 1‖ ≤ (k : ℝ) * ‖z - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have heq : z ^ (k + 1) - 1 = z * (z ^ k - 1) + (z - 1) := by ring
    rw [heq]
    calc
      _ ≤ ‖z * (z ^ k - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ = ‖z ^ k - 1‖ + ‖z - 1‖ := by rw [norm_mul, hz, one_mul]
      _ ≤ (k : ℝ) * ‖z - 1‖ + ‖z - 1‖ := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

/-- A nontrivial `ell`th root of unity is separated from one by at least
 `1/ell`. This deliberately coarse bound is enough for separated weights. -/
theorem one_le_mul_norm_unity_sub_one (ell : ℕ) (hell : ell ≠ 0)
    (z : ℂ) (hz : z ^ ell = 1) (hne : z ≠ 1) :
    1 ≤ (ell : ℝ) * ‖z - 1‖ := by
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hz hell
  have hgeom := geom_sum_mul z ell
  rw [hz, sub_self] at hgeom
  have hsum : (∑ k ∈ Finset.range ell, z ^ k) = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
  have hdiff : (∑ k ∈ Finset.range ell, (1 - z ^ k)) = (ell : ℂ) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hb : (ell : ℝ) ≤ (ell : ℝ) * ((ell : ℝ) * ‖z - 1‖) := by
    calc
      _ = ‖∑ k ∈ Finset.range ell, (1 - z ^ k)‖ := by rw [hdiff]; simp
      _ ≤ ∑ k ∈ Finset.range ell, ‖1 - z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range ell, (ell : ℝ) * ‖z - 1‖ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_sub_rev]
        exact (norm_pow_sub_one_le z hnorm k).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) (norm_nonneg _))
      _ = _ := by simp
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hb)
    (by exact_mod_cast Nat.pos_of_ne_zero hell : 0 < (ell : ℝ))

/-- Any two distinct roots of unity of the same order have the same
 uniform separation bound. -/
theorem one_le_mul_norm_unity_sub (ell : ℕ) (hell : ell ≠ 0)
    (z w : ℂ) (hz : z ^ ell = 1) (hw : w ^ ell = 1) (hne : z ≠ w) :
    1 ≤ (ell : ℝ) * ‖z - w‖ := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow hell] at hw
    exact zero_ne_one hw
  have hratio : (z / w) ^ ell = 1 := by rw [div_pow, hz, hw, div_self one_ne_zero]
  have hratio1 : z / w ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hw0).mp h)
  have h := one_le_mul_norm_unity_sub_one ell hell (z / w) hratio hratio1
  have hdist : ‖z / w - 1‖ = ‖z - w‖ := by
    rw [div_sub_one hw0, norm_div, Complex.norm_eq_one_of_pow_eq_one hw hell, div_one]
  rwa [hdist] at h

end LeanCanny.CountingHierarchy
