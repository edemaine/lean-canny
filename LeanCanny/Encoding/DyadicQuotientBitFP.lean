/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryPowModFP
public import LeanCanny.Encoding.BinaryDivFP

/-!
# FP access to bits of an exponentially long dyadic quotient

Input `pair a (pair b (pair p k))` requests bit `k` of `floor(2^p*a/m)`,
where `m=fromBitsLE b+1` and `a<m`. Repeated squaring modulo `2*m` computes
the selected bit; the power and quotient themselves are never written.
The output is the canonical natural code for zero or one. FP holds on every
raw string, and the semantic contract permits arbitrary binary words.
-/

@[expose] public section

namespace LeanCanny.Encoding.DyadicQuotientBits
open Complexity

theorem quotient_div_power (a m p k : ℕ) (hk : k ≤ p) :
    (2 ^ p * a / m) / 2 ^ k = 2 ^ (p - k) * a / m := by
  have hp : 2 ^ p = 2 ^ (p - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [Nat.div_div_eq_div_mul, hp,
    show 2 ^ (p - k) * 2 ^ k * a = (2 ^ (p - k) * a) * 2 ^ k by ring,
    Nat.mul_div_mul_right _ _ (by positivity)]

theorem testBit_quotient_of_le (a m p k : ℕ) (hk : k ≤ p) :
    (2 ^ p * a / m).testBit k = decide ((2 ^ (p - k) * a % (m * 2)) / m = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, quotient_div_power a m p k hk,
    Nat.mod_mul_right_div_self]

theorem testBit_quotient_of_lt (a m p k : ℕ) (ha : a < m) (hk : p < k) :
    (2 ^ p * a / m).testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have h : 2 ^ p * a / m < 2 ^ p := by
    apply Nat.div_lt_iff_lt_mul (by omega) |>.mpr
    exact Nat.mul_lt_mul_of_pos_left ha (by positivity)
  exact h.trans_le (Nat.pow_le_pow_right (by decide) hk.le)

def numerator (q : List Bool) : List Bool := pairFst q
def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairFst (pairSnd q))
def precision (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def index (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
def doubleModulus (q : List Bool) : List Bool := BinaryNat.add (pair (modulus q) (modulus q))
def powerQuery (q : List Bool) : List Bool :=
  pair [false, true] (pair (BinaryNat.sub (pair (precision q) (index q))) (BinaryNat.pred (doubleModulus q)))
def residue (q : List Bool) : List Bool := BinaryNat.mod
  (pair (BinaryNat.mul (pair (BinaryNat.powMod (powerQuery q)) (numerator q))) (doubleModulus q))
def digit (q : List Bool) : List Bool := BinaryNat.div (pair (residue q) (modulus q))
def value (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (index q) ≤ Nat.fromBitsLE (precision q) then digit q else []

theorem numerator_mem_FP : numerator ∈ FP := pairFst_mem_FP
theorem modulus_mem_FP : modulus ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.succ_mem_FP
theorem precision_mem_FP : precision ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem index_mem_FP : index ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem doubleModulus_mem_FP : doubleModulus ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP modulus_mem_FP) BinaryNat.add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem powerQuery_mem_FP : powerQuery ∈ FP := by
  have he := mem_FP_comp (mem_FP_pair precision_mem_FP index_mem_FP) BinaryNat.sub_mem_FP
  have hm := mem_FP_comp doubleModulus_mem_FP BinaryNat.pred_mem_FP
  have h := mem_FP_pair (constFn_mem_FP [false, true]) (mem_FP_pair he hm)
  refine mem_FP_of_eq (g := powerQuery) h ?_
  intro q
  simp only [Function.comp_apply, powerQuery]

theorem residue_mem_FP : residue ∈ FP := by
  have hp := mem_FP_comp powerQuery_mem_FP BinaryNat.powMod_mem_FP
  have hm := mem_FP_comp (mem_FP_pair hp numerator_mem_FP) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm doubleModulus_mem_FP) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := residue) h ?_
  intro q
  simp only [Function.comp_apply, residue]

theorem digit_mem_FP : digit ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair residue_mem_FP modulus_mem_FP) BinaryNat.div_mem_FP
  refine mem_FP_of_eq (g := digit) h ?_
  intro q
  simp only [Function.comp_apply, digit]

theorem value_mem_FP : value ∈ FP :=
  (BinaryNat.le_fppred index_mem_FP precision_mem_FP).ite_mem_FP digit_mem_FP (constFn_mem_FP [])

theorem residue_eq (q : List Bool) : residue q =
    (2 ^ (Nat.fromBitsLE (precision q) - Nat.fromBitsLE (index q)) * Nat.fromBitsLE (numerator q) %
      ((Nat.fromBitsLE (pairFst (pairSnd q)) + 1) * 2)).bits := by
  have hd : Nat.fromBitsLE (doubleModulus q) = (Nat.fromBitsLE (pairFst (pairSnd q)) + 1) * 2 := by
    simp only [doubleModulus, BinaryNat.add_eq_bits, pairFst_pair, pairSnd_pair, modulus,
      BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
    omega
  simp only [residue, BinaryNat.mod_pair, BinaryNat.mul_eq_bits, pairFst_pair, pairSnd_pair,
    Nat.fromBitsLE_bits, BinaryNat.powMod_eq_bits, powerQuery, BinaryNat.sub_eq_bits,
    BinaryNat.pred_eq_bits, hd]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ (Nat.fromBitsLE (pairFst (pairSnd q)) + 1) * 2)]
  simp only [show Nat.fromBitsLE [false, true] = 2 from rfl, Nat.mul_mod, Nat.mod_mod]

theorem value_eq (q : List Bool)
    (ha : Nat.fromBitsLE (numerator q) < Nat.fromBitsLE (pairFst (pairSnd q)) + 1) :
    value q =
      (if (2 ^ Nat.fromBitsLE (precision q) * Nat.fromBitsLE (numerator q) /
        (Nat.fromBitsLE (pairFst (pairSnd q)) + 1)).testBit (Nat.fromBitsLE (index q)) then [true] else []) := by
  let a := Nat.fromBitsLE (numerator q)
  let m := Nat.fromBitsLE (pairFst (pairSnd q)) + 1
  let p := Nat.fromBitsLE (precision q)
  let k := Nat.fromBitsLE (index q)
  change (if k ≤ p then digit q else []) = if (2 ^ p * a / m).testBit k then [true] else []
  by_cases hk : k ≤ p
  · rw [ite_eq_left hk, testBit_quotient_of_le a m p k hk]
    have hd : digit q = ((2 ^ (p - k) * a % (m * 2)) / m).bits := by
      simp only [digit, BinaryNat.div_eq_bits, pairFst_pair, pairSnd_pair, residue_eq,
        Nat.fromBitsLE_bits, modulus, BinaryNat.succ_eq_bits, a, m, p, k]
    rw [hd, Nat.mod_mul_right_div_self]
    have hsmall := Nat.mod_lt (2 ^ (p - k) * a / m) (by decide : 0 < 2)
    have hc : (2 ^ (p - k) * a / m) % 2 = 0 ∨ (2 ^ (p - k) * a / m) % 2 = 1 := by omega
    rcases hc with h | h <;> simp [h]
  · rw [ite_eq_right hk, testBit_quotient_of_lt a m p k ha (by omega)]
    rfl

theorem value_pair (a b p k : List Bool) (ha : Nat.fromBitsLE a < Nat.fromBitsLE b + 1) :
    value (pair a (pair b (pair p k))) =
      if (2 ^ Nat.fromBitsLE p * Nat.fromBitsLE a / (Nat.fromBitsLE b + 1)).testBit (Nat.fromBitsLE k)
        then [true] else [] := by
  have h := value_eq (pair a (pair b (pair p k)))
    (by simpa only [numerator, pairFst_pair, pairSnd_pair] using ha)
  simpa only [numerator, precision, index, pairFst_pair, pairSnd_pair] using h

end LeanCanny.Encoding.DyadicQuotientBits
