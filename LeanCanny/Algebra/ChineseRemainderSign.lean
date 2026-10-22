/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderSum

/-!
# Sign reconstruction using truncated CRT fractions

Replacing each local fraction `a/m` by `floor(D*a/m)/D` incurs total downward
error at most `card(ι)/D`. If `D > 2*card(ι)*product`, the half-interval test
still determines the sign of a nonzero integer of magnitude below `product/2`.
In particular, dyadic precision turns sign reconstruction into a half-interval
comparison for a sum of integer quotients modulo a power of two. This is a
correctness reduction; the streamed quotient/sum-bit algorithm and its space
certificate are separate obligations.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder

open scoped BigOperators

theorem quotient_error (n m D : ℕ) (hD : 0 < D) :
    0 ≤ (n : ℚ) / m - ((D * n / m : ℕ) : ℚ) / D ∧
    (n : ℚ) / m - ((D * n / m : ℕ) : ℚ) / D ≤ 1 / D := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hf : ⌊(D : ℚ) * ((n : ℚ) / m)⌋ = (D * n / m : ℕ) := by
    rw [← mul_div_assoc, ← Nat.cast_mul, Rat.floor_natCast_div_natCast]
    exact (Int.natCast_ediv _ _).symm
  have hlo := Int.floor_le ((D : ℚ) * ((n : ℚ) / m))
  have hhi := Int.lt_floor_add_one ((D : ℚ) * ((n : ℚ) / m))
  rw [hf, Int.cast_natCast] at hlo hhi
  constructor
  · rw [sub_nonneg, div_le_iff₀ hDQ]
    nlinarith
  · rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hDQ]
    nlinarith

namespace System

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : System ι)

def truncatedSum (r : ι → ℕ) (D : ℕ) : ℕ :=
  ∑ i, D * F.numerator r i / F.modulus i

theorem truncatedSum_error (r : ι → ℕ) (D : ℕ) (hD : 0 < D) :
    0 ≤ F.fractionSum r - (F.truncatedSum r D : ℚ) / D ∧
    F.fractionSum r - (F.truncatedSum r D : ℚ) / D ≤ (Fintype.card ι : ℚ) / D := by
  simp only [fractionSum, truncatedSum, Nat.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (quotient_error _ _ D hD).1)
  · calc
      _ ≤ ∑ _i : ι, (1 : ℚ) / D := Finset.sum_le_sum (fun i _ => (quotient_error _ _ D hD).2)
      _ = _ := by simp [div_eq_mul_inv]

theorem negative_iff_half_lt_truncated (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product) (hne : z ≠ 0)
    (D : ℕ) (hD : 0 < D) (hprecision : 2 * Fintype.card ι * F.product < D) :
    z < 0 ↔ (1 / 2 : ℚ) < Int.fract ((F.truncatedSum r D : ℚ) / D) := by
  have : NeZero F.product := ⟨F.product_pos.ne'⟩
  apply IntegerModular.negative_iff_half_lt_fract_approx z hz hne (F.fractionSum r)
    ((F.truncatedSum r D : ℚ) / D) (F.fract_fractionSum r z hr)
  have herror := F.truncatedSum_error r D hD
  refine ⟨herror.1, herror.2.trans_lt ?_⟩
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hPQ : (0 : ℚ) < F.product := by exact_mod_cast F.product_pos
  apply (div_lt_div_iff₀ hDQ (by positivity)).mpr
  have hp : (2 : ℚ) * Fintype.card ι * F.product < D := by exact_mod_cast hprecision
  nlinarith

theorem negative_iff_truncated_mod (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product) (hne : z ≠ 0)
    (D : ℕ) (hD : 0 < D) (hprecision : 2 * Fintype.card ι * F.product < D) :
    z < 0 ↔ D < 2 * (F.truncatedSum r D % D) := by
  rw [F.negative_iff_half_lt_truncated r z hr hz hne D hD hprecision,
    Int.fract_div_natCast_eq_div_natCast_mod]
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  rw [lt_div_iff₀ hDQ]
  constructor
  · intro h
    have hq : (D : ℚ) < 2 * (F.truncatedSum r D % D : ℕ) := by linarith
    exact_mod_cast hq
  · intro h
    have hq : (D : ℚ) < 2 * (F.truncatedSum r D % D : ℕ) := by exact_mod_cast h
    linarith

end System
end LeanCanny.Algebra.ChineseRemainder
