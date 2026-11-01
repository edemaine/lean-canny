/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.IntegralCoordinateBasisFinStep

/-! # Literal chart ranks and the two nilpotent basis digits -/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthChartMonomial
open LeanCanny.Encoding FixedWidthPolynomial IntegralCoordinateBasis

theorem base_le_count (n W : ℕ) : 2 ^ W ≤ count (n + 1) W := by
  unfold count
  rw [pow_succ]
  exact (Nat.one_mul _).symm.trans_le (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)))

theorem chart_vector (n W D : ℕ) (hD : D < 2 ^ W) :
    vector (n + 1) W ⟨D, hD.trans_le (base_le_count n W)⟩ = Finsupp.single 0 D := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [vector_apply, Fin.val_zero, Nat.zero_mul, pow_zero, Nat.div_one,
      Nat.mod_eq_of_lt hD, Finsupp.single_eq_same]
  · have HE : W ≤ (j.val + 1) * W := (Nat.one_mul W).symm.trans_le (Nat.mul_le_mul_right W (by omega))
    have HP := hD.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) HE)
    simp only [vector_apply, Fin.val_succ, Nat.div_eq_of_lt HP, Nat.zero_mod]
    exact (Finsupp.single_eq_of_ne (by intro h; have H := congrArg Fin.val h; simp at H)).symm

theorem vector_eq_chart_iff (n W D : ℕ) (hD : D < 2 ^ W) (k : Fin (count (n + 1) W)) :
    vector (n + 1) W k = Finsupp.single 0 D ↔ k.val = D := by
  rw [← chart_vector n W D hD, (vector_injective (n + 1) W).eq_iff, Fin.ext_iff]

theorem native_eq_chart_iff (n W D : ℕ) (hD : D < 2 ^ W) (k : Fin (count (n + 1) W)) :
    nativeExponent (Equiv.refl (Fin (n + 1))) W k.val = Finsupp.single 0 D ↔ k.val = D := by
  rw [nativeExponent_refl, entry_vector, vector_eq_chart_iff n W D hD]

theorem pair_div (m B : ℕ) (u : Fin (count m B)) (a : Fin (2 ^ B)) :
    (pairIndex m B (u, a)).val / 2 ^ B = u.val := by
  change (a.val + 2 ^ B * u.val) / 2 ^ B = u.val
  rw [Nat.add_comm a.val, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt a.isLt, Nat.add_zero]

theorem pair_mod (m B : ℕ) (u : Fin (count m B)) (a : Fin (2 ^ B)) :
    (pairIndex m B (u, a)).val % 2 ^ B = a.val := by
  change (a.val + 2 ^ B * u.val) % 2 ^ B = a.val
  rw [Nat.add_comm a.val, Nat.mul_add_mod, Nat.mod_eq_of_lt a.isLt]

end LeanCanny.Algebra.FixedWidthChartMonomial
