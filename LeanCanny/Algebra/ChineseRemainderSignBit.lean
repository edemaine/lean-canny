/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderSign
public import LeanCanny.Algebra.SmallModulusCRT

/-!
# One bit of the truncated CRT sum determines the sign

The strict magnitude bound also excludes equality with the half threshold.
Consequently sign reconstruction needs one selected sum bit, without a scan
of all lower bits. Vanishing local numerators cover zero as well.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerModular

theorem fract_lt_half_of_nonneg {M : ℕ} [NeZero M] (z : ℤ)
    (hz : 2 * z.natAbs < M) (hzz : 0 ≤ z) : Int.fract ((z : ℚ) / M) < 1 / 2 := by
  have hM : (0 : ℚ) < M := by exact_mod_cast NeZero.pos M
  have hc := valMinAbs_intCast z hz
  have hr : (z : ZMod M).val ≤ M / 2 := (ZMod.valMinAbs_nonneg_iff _).mp (by rwa [hc])
  rw [ZMod.valMinAbs_def_pos, ite_eq_left hr] at hc
  have ha : z.natAbs = (z : ZMod M).val := by
    simpa only [Int.natAbs_natCast] using (congrArg Int.natAbs hc).symm
  have hlt : (2 : ℚ) * ((z : ZMod M).val : ℚ) < M := by exact_mod_cast (ha ▸ hz)
  rw [fract_intCast_div, div_lt_iff₀ hM]
  linarith

theorem negative_iff_half_le_fract_approx {M : ℕ} [NeZero M] (z : ℤ)
    (hz : 2 * z.natAbs < M) (hne : z ≠ 0) (S A : ℚ)
    (hS : Int.fract S = ((z : ZMod M).val : ℚ) / M)
    (hA : 0 ≤ S - A ∧ S - A < 1 / (2 * (M : ℚ))) :
    z < 0 ↔ (1 / 2 : ℚ) ≤ Int.fract A := by
  constructor
  · exact fun h => ((negative_iff_half_lt_fract_approx z hz hne S A hS hA).mp h).le
  · intro hhalf
    by_contra hzneg
    have hslt : Int.fract S < 1 / 2 := by
      rw [hS, ← fract_intCast_div]
      exact fract_lt_half_of_nonneg z hz (by omega)
    have hM : (0 : ℚ) < M := by exact_mod_cast NeZero.pos M
    have hr : (1 : ℚ) ≤ (z : ZMod M).val := by exact_mod_cast val_intCast_pos z hz hne
    have he : S - A < Int.fract S := by
      apply hA.2.trans
      rw [hS]
      apply (div_lt_div_iff₀ (by positivity) hM).mpr
      nlinarith
    have hfract : Int.fract A = Int.fract S - (S - A) := by
      apply Int.fract_eq_iff.mpr
      refine ⟨by linarith, ?_, ⌊S⌋, ?_⟩
      · have := Int.fract_lt_one S
        linarith [hA.1]
      · unfold Int.fract
        ring
    rw [hfract] at hhalf
    linarith [hA.1]

end LeanCanny.Algebra.IntegerModular

namespace LeanCanny.Algebra.ChineseRemainder.System

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : System ι)

theorem negative_iff_half_le_truncated (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product) (hne : z ≠ 0)
    (D : ℕ) (hD : 0 < D) (hprecision : 2 * Fintype.card ι * F.product < D) :
    z < 0 ↔ (1 / 2 : ℚ) ≤ Int.fract ((F.truncatedSum r D : ℚ) / D) := by
  have : NeZero F.product := ⟨F.product_pos.ne'⟩
  apply IntegerModular.negative_iff_half_le_fract_approx z hz hne (F.fractionSum r)
    ((F.truncatedSum r D : ℚ) / D) (F.fract_fractionSum r z hr)
  have herror := F.truncatedSum_error r D hD
  refine ⟨herror.1, herror.2.trans_lt ?_⟩
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hPQ : (0 : ℚ) < F.product := by exact_mod_cast F.product_pos
  apply (div_lt_div_iff₀ hDQ (by positivity)).mpr
  have hp : (2 : ℚ) * Fintype.card ι * F.product < D := by exact_mod_cast hprecision
  nlinarith

theorem negative_iff_truncated_testBit (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product) (hne : z ≠ 0)
    (k : ℕ) (hprecision : 2 * Fintype.card ι * F.product < 2 ^ (k + 1)) :
    z < 0 ↔ (F.truncatedSum r (2 ^ (k + 1))).testBit k = true := by
  rw [F.negative_iff_half_le_truncated r z hr hz hne _ (by positivity) hprecision,
    Int.fract_div_natCast_eq_div_natCast_mod]
  have hD : (0 : ℚ) < (2 ^ (k + 1) : ℕ) := by positivity
  rw [le_div_iff₀ hD]
  have he : (1 / 2 : ℚ) * (2 ^ (k + 1) : ℕ) = (2 ^ k : ℕ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [he, Nat.cast_le]
  let T := F.truncatedSum r (2 ^ (k + 1))
  change 2 ^ k ≤ T % 2 ^ (k + 1) ↔ T.testBit k = true
  have hbit : (T % 2 ^ (k + 1)).testBit k = T.testBit k := by simp
  rw [← hbit]
  exact ⟨fun h => Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h (Nat.mod_lt _ (by positivity)),
    fun h => Nat.ge_two_pow_of_testBit h⟩

theorem numerator_eq_zero (r : ι → ℕ) (i : ι) (hr : (r i : ZMod (F.modulus i)) = 0) :
    F.numerator r i = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact dvd_mul_of_dvd_left ((ZMod.natCast_eq_zero_iff _ _).mp hr) _

/-- The actual CRT construction handles zero without a separate zero oracle:
all its locally reduced numerators vanish. -/
theorem negative_iff_truncated_bit (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product)
    (k : ℕ) (hprecision : 2 * Fintype.card ι * F.product < 2 ^ (k + 1)) :
    z < 0 ↔ (F.truncatedSum r (2 ^ (k + 1))).testBit k = true := by
  by_cases hzero : z = 0
  · subst z
    have hn : ∀ i, F.numerator r i = 0 := fun i =>
      F.numerator_eq_zero r i (by simpa only [Int.cast_zero] using hr i)
    simp [truncatedSum, hn]
  · exact F.negative_iff_truncated_testBit r z hr hz hzero k hprecision

end LeanCanny.Algebra.ChineseRemainder.System

namespace LeanCanny.Algebra.ChineseRemainder

theorem negative_iff_small_truncated_testBit (z : ℤ) (B : ℕ) (hb : z.natAbs.size ≤ B)
    (r : SmallPrime (2 * B + 6) → ℕ)
    (hr : ∀ p, (r p : ZMod ((primePowerSystem (2 * B + 6)).modulus p)) = z) :
    z < 0 ↔ ((primePowerSystem (2 * B + 6)).truncatedSum r (2 ^ precisionBits (2 * B + 6))).testBit
      (precisionBits (2 * B + 6) - 1) = true := by
  have hp : precisionBits (2 * B + 6) - 1 + 1 = precisionBits (2 * B + 6) := by
    dsimp only [precisionBits]
    omega
  have hz : 2 * z.natAbs < (primePowerSystem (2 * B + 6)).product := by
    rw [primePowerSystem_product]
    exact IntegerModular.two_natAbs_lt_lcmUpto z B hb
  have hc : 2 * Fintype.card (SmallPrime (2 * B + 6)) * (primePowerSystem (2 * B + 6)).product <
      2 ^ (precisionBits (2 * B + 6) - 1 + 1) := by
    rw [hp]
    exact precision_sufficient _
  simpa only [hp] using (primePowerSystem (2 * B + 6)).negative_iff_truncated_bit r z hr hz _ hc

end LeanCanny.Algebra.ChineseRemainder
