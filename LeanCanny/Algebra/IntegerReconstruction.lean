/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerModular
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor

/-!
# Integer reconstruction and sign from a sufficiently large modulus

These are mathematical specifications for residue reconstruction. They do not
store or compute the (potentially exponentially long) combined residue. A
streamed CRT implementation must implement the fractional-part specification
without materializing that residue.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerModular

theorem valMinAbs_intCast {M : ℕ} [NeZero M] (z : ℤ) (hz : 2 * z.natAbs < M) :
    (z : ZMod M).valMinAbs = z := by
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  all_goals have habs := Int.natCast_natAbs z; have hb : (2 : ℤ) * z.natAbs < M := by exact_mod_cast hz
  · have := neg_abs_le z
    omega
  · have := le_abs_self z
    omega

theorem negative_iff_half_lt_val {M : ℕ} [NeZero M] (z : ℤ) (hz : 2 * z.natAbs < M) :
    z < 0 ↔ M / 2 < (z : ZMod M).val := by
  have h := (ZMod.valMinAbs_nonneg_iff (z : ZMod M)).not
  rw [valMinAbs_intCast z hz] at h
  simpa only [not_le] using h

theorem fract_intCast_div (z : ℤ) {M : ℕ} [NeZero M] :
    Int.fract ((z : ℚ) / M) = ((z : ZMod M).val : ℚ) / M := by
  rw [Int.fract_div_intCast_eq_div_intCast_mod]
  congr 1
  exact_mod_cast (ZMod.val_intCast z).symm

theorem negative_iff_half_lt_fract {M : ℕ} [NeZero M] (z : ℤ) (hz : 2 * z.natAbs < M) :
    z < 0 ↔ (1 / 2 : ℚ) < Int.fract ((z : ℚ) / M) := by
  rw [fract_intCast_div]
  have hM : (0 : ℚ) < M := by exact_mod_cast NeZero.pos M
  rw [negative_iff_half_lt_val z hz, lt_div_iff₀ hM]
  have hhalf : M / 2 < (z : ZMod M).val ↔ M < 2 * (z : ZMod M).val := by omega
  rw [hhalf]
  constructor
  · intro h
    have hc : (M : ℚ) < 2 * ((z : ZMod M).val : ℚ) := by exact_mod_cast h
    linarith
  · intro h
    have hc : (M : ℚ) < 2 * ((z : ZMod M).val : ℚ) := by linarith
    exact_mod_cast hc

theorem two_natAbs_lt_lcmUpto (z : ℤ) (B : ℕ) (hb : z.natAbs.size ≤ B) :
    2 * z.natAbs < Nat.lcmUpto (2 * B + 6) := by
  have h := Nat.size_le.mp hb
  have hL := two_pow_lt_lcmUpto (B + 1)
  rw [pow_succ] at hL
  convert lt_trans (by omega : 2 * z.natAbs < 2 ^ B * 2) hL using 1

theorem val_intCast_pos {M : ℕ} [NeZero M] (z : ℤ) (hz : 2 * z.natAbs < M) (hne : z ≠ 0) :
    0 < (z : ZMod M).val := by
  by_contra h
  have he : (z : ZMod M) = 0 := (ZMod.val_eq_zero _).mp (by omega)
  have hc := valMinAbs_intCast z hz
  rw [he, ZMod.valMinAbs_zero] at hc
  exact hne hc.symm

/-- A downward approximation accurate to less than `1/(2*M)` preserves the
sign comparison, provided zero has been tested separately. -/
theorem negative_iff_half_lt_fract_approx {M : ℕ} [NeZero M] (z : ℤ)
    (hz : 2 * z.natAbs < M) (hne : z ≠ 0) (S A : ℚ)
    (hS : Int.fract S = ((z : ZMod M).val : ℚ) / M)
    (hA : 0 ≤ S - A ∧ S - A < 1 / (2 * (M : ℚ))) :
    z < 0 ↔ (1 / 2 : ℚ) < Int.fract A := by
  have hM : (0 : ℚ) < M := by exact_mod_cast NeZero.pos M
  have hr : (1 : ℚ) ≤ (z : ZMod M).val := by exact_mod_cast val_intCast_pos z hz hne
  have he : S - A < Int.fract S := by
    rw [hS]
    have hsmall : 1 / (2 * (M : ℚ)) < ((z : ZMod M).val : ℚ) / M := by
      apply (div_lt_div_iff₀ (by positivity) hM).mpr
      nlinarith
    exact hA.2.trans hsmall
  have hfract : Int.fract A = Int.fract S - (S - A) := by
    apply Int.fract_eq_iff.mpr
    refine ⟨by linarith, ?_, ⌊S⌋, ?_⟩
    · have := Int.fract_lt_one S
      linarith [hA.1]
    · unfold Int.fract
      ring
  constructor
  · intro hneg
    have hv := (negative_iff_half_lt_val z hz).mp hneg
    have hgap : M + 1 ≤ 2 * (z : ZMod M).val := by omega
    have hgapQ : (M : ℚ) + 1 ≤ 2 * ((z : ZMod M).val : ℚ) := by exact_mod_cast hgap
    have hsep : (1 / 2 : ℚ) + 1 / (2 * (M : ℚ)) ≤ Int.fract S := by
      rw [hS, le_div_iff₀ hM]
      field_simp
      nlinarith
    rw [hfract]
    linarith [hA.2]
  · intro hneg
    have hs : (1 / 2 : ℚ) < Int.fract S := by rw [hfract] at hneg; linarith [hA.1]
    apply (negative_iff_half_lt_fract z hz).mpr
    rwa [fract_intCast_div, ← hS]

end LeanCanny.Algebra.IntegerModular
