/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerReconstruction
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# CRT reconstruction as a sum of small fractions

Each numerator is reduced modulo its own modulus after multiplying by a local
inverse. The fractional part of their rational sum is the combined residue
divided by the product modulus. The large product is used in the specification,
not claimed to be stored by a polynomial-space algorithm.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder

open scoped BigOperators

structure System (ι : Type*) where
  modulus : ι → ℕ
  positive : ∀ i, 0 < modulus i
  coprime : Pairwise (fun i j => (modulus i).Coprime (modulus j))

namespace System

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : System ι)

def product : ℕ := ∏ i, F.modulus i

def cofactor (i : ι) : ℕ := ∏ j ∈ Finset.univ.erase i, F.modulus j

def inverse (i : ι) : ℕ := ((F.cofactor i : ZMod (F.modulus i))⁻¹).val

def numerator (r : ι → ℕ) (i : ι) : ℕ := (r i * F.inverse i) % F.modulus i

def integerSum (r : ι → ℕ) : ℕ := ∑ i, F.numerator r i * F.cofactor i

def fractionSum (r : ι → ℕ) : ℚ := ∑ i, (F.numerator r i : ℚ) / F.modulus i

omit [DecidableEq ι] in
theorem product_pos : 0 < F.product := Finset.prod_pos (fun i _ => F.positive i)

theorem cofactor_mul (i : ι) : F.cofactor i * F.modulus i = F.product :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem cofactor_coprime (i : ι) : (F.cofactor i).Coprime (F.modulus i) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  exact F.coprime (Finset.mem_erase.mp hj).1

theorem inverse_mul (i : ι) :
    (F.inverse i : ZMod (F.modulus i)) * (F.cofactor i : ZMod (F.modulus i)) = 1 := by
  exact ZMod.val_inv_mul (F.cofactor_coprime i)

theorem numerator_lt (r : ι → ℕ) (i : ι) : F.numerator r i < F.modulus i :=
  Nat.mod_lt _ (F.positive i)

theorem integerSum_cast (r : ι → ℕ) (i : ι) :
    (F.integerSum r : ZMod (F.modulus i)) = r i := by
  simp only [integerSum, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_eq_single i]
  · rw [numerator, ZMod.natCast_mod, Nat.cast_mul, mul_assoc, F.inverse_mul, mul_one]
  · intro j _ hji
    have hd : F.modulus i ∣ F.cofactor j :=
      Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩)
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero]
  · simp

theorem integerSum_cast_product (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) :
    (F.integerSum r : ZMod F.product) = z := by
  have hd : (F.product : ℤ) ∣ z - (F.integerSum r : ℤ) := by
    change ((∏ i, F.modulus i : ℕ) : ℤ) ∣ _
    rw [Nat.cast_prod]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (F.coprime hij).isCoprime
    · intro i
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      simpa only [Int.cast_natCast] using (F.integerSum_cast r i).trans (hr i)
  simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hd

theorem fractionSum_eq (r : ι → ℕ) : F.fractionSum r = (F.integerSum r : ℚ) / F.product := by
  have hP : (F.product : ℚ) ≠ 0 := by exact_mod_cast F.product_pos.ne'
  rw [eq_div_iff hP]
  simp only [fractionSum, integerSum, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hm : (F.modulus i : ℚ) ≠ 0 := by exact_mod_cast (F.positive i).ne'
  have hp : (F.product : ℚ) = F.cofactor i * F.modulus i := by
    exact_mod_cast (F.cofactor_mul i).symm
  rw [hp]
  field_simp

theorem fract_fractionSum (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) :
    Int.fract (F.fractionSum r) = ((z : ZMod F.product).val : ℚ) / F.product := by
  have : NeZero F.product := ⟨F.product_pos.ne'⟩
  rw [F.fractionSum_eq, Int.fract_div_natCast_eq_div_natCast_mod]
  have h := congrArg ZMod.val (F.integerSum_cast_product r z hr)
  rw [ZMod.val_natCast] at h
  rw [h]

theorem negative_iff_half_lt_fract (r : ι → ℕ) (z : ℤ)
    (hr : ∀ i, (r i : ZMod (F.modulus i)) = z) (hz : 2 * z.natAbs < F.product) :
    z < 0 ↔ (1 / 2 : ℚ) < Int.fract (F.fractionSum r) := by
  have : NeZero F.product := ⟨F.product_pos.ne'⟩
  rw [F.fract_fractionSum r z hr, ← IntegerModular.fract_intCast_div z]
  exact IntegerModular.negative_iff_half_lt_fract z hz

end System
end LeanCanny.Algebra.ChineseRemainder
