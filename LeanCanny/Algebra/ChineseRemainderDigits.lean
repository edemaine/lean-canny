/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderSignBit

/-!
# Exact integer reconstruction from truncated CRT sums

The truncation error has an integer expression as a sum of local remainders
times cofactors. Precision larger than the number of moduli times their product
makes upward rounding recover the full CRT integer sum exactly. These identities
are the arithmetic specification for digit recovery; their large operands still
require streamed bit algorithms.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder.System
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : System ι)

def truncationError (r : ι → ℕ) (D : ℕ) : ℕ :=
  ∑ i, F.cofactor i * (D * F.numerator r i % F.modulus i)

theorem truncatedSum_exact (r : ι → ℕ) (D : ℕ) :
    D * F.integerSum r = F.product * F.truncatedSum r D + F.truncationError r D := by
  unfold integerSum truncatedSum truncationError
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    D * (F.numerator r i * F.cofactor i) = F.cofactor i * (D * F.numerator r i) := by ring
    _ = F.cofactor i * (D * F.numerator r i % F.modulus i +
        F.modulus i * (D * F.numerator r i / F.modulus i)) := by rw [Nat.mod_add_div]
    _ = F.product * (D * F.numerator r i / F.modulus i) +
        F.cofactor i * (D * F.numerator r i % F.modulus i) := by rw [← F.cofactor_mul i]; ring

theorem truncationError_le (r : ι → ℕ) (D : ℕ) :
    F.truncationError r D ≤ Fintype.card ι * F.product := by
  calc
    _ ≤ ∑ _i : ι, F.product := Finset.sum_le_sum (fun i _ =>
      (Nat.mul_le_mul_left (F.cofactor i) (Nat.mod_lt _ (F.positive i)).le).trans_eq (F.cofactor_mul i))
    _ = _ := by simp

theorem integerSum_eq_rounded_truncated (r : ι → ℕ) (D : ℕ) (hD : 0 < D)
    (hprecision : Fintype.card ι * F.product < D) :
    F.integerSum r = (F.product * F.truncatedSum r D + D - 1) / D := by
  have he := F.truncatedSum_exact r D
  have herr := (F.truncationError_le r D).trans_lt hprecision
  symm
  apply (Nat.div_eq_iff hD).mpr
  have hsub := Nat.sub_add_cancel (by omega : 1 ≤ F.product * F.truncatedSum r D + D)
  have hsub' := Nat.sub_add_cancel (by omega : 1 ≤ F.integerSum r * D + D)
  constructor <;> nlinarith

theorem residue_eq_rounded_truncated (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (D : ℕ) (hD : 0 < D)
    (hprecision : Fintype.card ι * F.product < D) :
    (z : ZMod F.product).val = ((F.product * F.truncatedSum r D + D - 1) / D) % F.product := by
  have hi := congrArg ZMod.val (F.integerSum_cast_product r z hr)
  rw [ZMod.val_natCast, F.integerSum_eq_rounded_truncated r D hD hprecision] at hi
  exact hi.symm

theorem numerator_zero_of_integerSum_mod_eq_zero (r : ι → ℕ) (hzero : F.integerSum r % F.product = 0)
    (i : ι) : F.numerator r i = 0 := by
  have hm : F.modulus i ∣ F.product := ⟨F.cofactor i, ((mul_comm _ _).trans (F.cofactor_mul i)).symm⟩
  have hd : F.modulus i ∣ F.integerSum r := hm.trans (Nat.dvd_of_mod_eq_zero hzero)
  apply F.numerator_eq_zero r i
  rw [← F.integerSum_cast r i]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd

theorem truncatedRank_le (r : ι → ℕ) (D : ℕ) (hD : 0 < D) :
    F.truncatedSum r D / D ≤ Fintype.card ι := by
  have hsum : F.truncatedSum r D ≤ Fintype.card ι * D := by
    have hterm (i : ι) : D * F.numerator r i / F.modulus i ≤ D := by
      apply Nat.div_le_of_le_mul
      have hi := Nat.mul_le_mul_left D (F.numerator_lt r i).le
      nlinarith
    unfold truncatedSum
    calc
      _ ≤ ∑ _i : ι, D := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp
  exact (Nat.div_le_div_right hsum).trans_eq (Nat.mul_div_cancel _ hD)

theorem truncatedRank_eq (r : ι → ℕ) (D : ℕ) (hD : 0 < D)
    (hprecision : Fintype.card ι * F.product < D) :
    F.truncatedSum r D / D = F.integerSum r / F.product := by
  by_cases hzero : F.integerSum r % F.product = 0
  · have hn := F.numerator_zero_of_integerSum_mod_eq_zero r hzero
    simp only [truncatedSum, integerSum, hn, mul_zero, zero_mul, Nat.zero_div, Finset.sum_const_zero]
  · let q := F.integerSum r / F.product
    have he := F.truncatedSum_exact r D
    have herr := (F.truncationError_le r D).trans_lt hprecision
    have hrem : 1 ≤ F.integerSum r % F.product := by omega
    have hexp : D * F.integerSum r = F.product * (q * D) + D * (F.integerSum r % F.product) := by
      calc
        _ = D * (F.integerSum r % F.product + F.product * q) := by rw [Nat.mod_add_div]
        _ = _ := by ring
    have hlow : q * D ≤ F.truncatedSum r D := by
      apply Nat.le_of_mul_le_mul_left _ F.product_pos
      have hr := Nat.mul_le_mul_left D hrem
      nlinarith
    have hhigh : F.truncatedSum r D < (q + 1) * D := by
      have hmod := Nat.mod_lt (F.integerSum r) F.product_pos
      have hi : F.integerSum r < (q + 1) * F.product := by
        have hid := Nat.mod_add_div (F.integerSum r) F.product
        change F.integerSum r % F.product + F.product * q = F.integerSum r at hid
        nlinarith
      have hmul := Nat.mul_lt_mul_of_pos_left hi hD
      apply Nat.lt_of_mul_lt_mul_left (a := F.product)
      nlinarith
    exact Nat.div_eq_of_lt_le hlow hhigh

theorem residue_eq_sub_truncatedRank (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (D : ℕ) (hD : 0 < D)
    (hprecision : Fintype.card ι * F.product < D) :
    (z : ZMod F.product).val = F.integerSum r - (F.truncatedSum r D / D) * F.product := by
  have hi := congrArg ZMod.val (F.integerSum_cast_product r z hr)
  rw [ZMod.val_natCast] at hi
  rw [← hi, F.truncatedRank_eq r D hD hprecision]
  exact Nat.mod_eq_sub_div_mul

theorem centered_reconstruction (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product)
    (D : ℕ) (hD : 0 < D) (hprecision : Fintype.card ι * F.product < D) :
    let x := F.integerSum r - (F.truncatedSum r D / D) * F.product
    (if x ≤ F.product / 2 then (x : ℤ) else (x : ℤ) - F.product) = z := by
  have : NeZero F.product := ⟨F.product_pos.ne'⟩
  have he := IntegerModular.valMinAbs_intCast z hz
  rw [ZMod.valMinAbs_def_pos, F.residue_eq_sub_truncatedRank r z hr D hD hprecision] at he
  exact he

theorem natAbs_digit_eq (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product)
    (D k : ℕ) (hD : 0 < D) (hprecision : Fintype.card ι * F.product < D) :
    let x := F.integerSum r - (F.truncatedSum r D / D) * F.product
    z.natAbs.testBit k =
      (if x ≤ F.product / 2 then (x : ℤ) else (x : ℤ) - F.product).natAbs.testBit k := by
  dsimp only
  rw [F.centered_reconstruction r z hr hz D hD hprecision]

end LeanCanny.Algebra.ChineseRemainder.System
