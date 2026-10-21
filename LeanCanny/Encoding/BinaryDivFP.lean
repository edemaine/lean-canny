/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryModFP

/-!
# Polynomial-time binary quotient and remainder

The quotient fold reads the dividend from high to low. At each position the
certified remainder routine determines the next quotient bit. Recomputing a
tail remainder still gives a polynomial-time fold, while retaining only one
canonical quotient word as its fold state. Every partial quotient has at most
the processed dividend's bit length. Division by zero follows `a / 0 = 0`.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat


theorem quotient_step (m t : ℕ) (hm : 0 < m) (bit : Bool) :
    (if m ≤ (if bit then 1 else 0) + 2 * (t % m) then 1 else 0) + 2 * (t / m) =
      ((if bit then 1 else 0) + 2 * t) / m := by
  have hr := Nat.mod_lt t hm
  have hu : (if bit then 1 else 0) + 2 * (t % m) < 2 * m := by
    cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hdecomp : (if bit then 1 else 0) + 2 * t =
      ((if bit then 1 else 0) + 2 * (t % m)) + m * (2 * (t / m)) := by
    have hd := Nat.mod_add_div t m
    nlinarith
  rw [hdecomp, Nat.add_mul_div_left _ _ hm]
  by_cases h : m ≤ (if bit then 1 else 0) + 2 * (t % m)
  · have hd : ((if bit then 1 else 0) + 2 * (t % m)) / m = 1 :=
      Nat.div_eq_of_lt_le (by simpa using h) (by simpa using hu)
    simp only [h, ↓reduceIte, hd]
  · have hd : ((if bit then 1 else 0) + 2 * (t % m)) / m = 0 := Nat.div_eq_of_lt (by omega)
    simp only [h, ↓reduceIte, hd]

def divDigit (m : List Bool) (bit : Bool) (q t : List Bool) : List Bool :=
  if Nat.fromBitsLE m = 0 then []
  else normalize ((decide (Nat.fromBitsLE m ≤ Nat.fromBitsLE (bit :: mod (pair t m)))) :: q)

def divFold (m : List Bool) : List Bool → List Bool
  | [] => []
  | bit :: t => divDigit m bit (divFold m t) t

theorem divFold_eq_bits (m t : List Bool) :
    divFold m t = (Nat.fromBitsLE t / Nat.fromBitsLE m).bits := by
  induction t with
  | nil => simp [divFold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit t ih =>
      by_cases hm : Nat.fromBitsLE m = 0
      · simp [divFold, divDigit, hm]
      · simp only [divFold, divDigit, hm, ↓reduceIte, normalize_eq_bits, Nat.fromBitsLE_cons,
          mod_pair, Nat.fromBitsLE_bits, decide_eq_true_eq, ih]
        rw [quotient_step _ _ (by omega) bit]

theorem divFold_length_le (m t : List Bool) : (divFold m t).length ≤ t.length := by
  rw [divFold_eq_bits, Nat.size_eq_bits_len]
  exact (Nat.size_le_size (Nat.div_le_self _ _)).trans
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length t))

theorem divDigit_mem_FP (bit : Bool) :
    (fun p => divDigit (pairFst (pairFst p)) bit (pairSnd (pairFst p)) (pairSnd p)) ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hq := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hr := mem_FP_comp (mem_FP_pair pairSnd_mem_FP hm) mod_mem_FP
  have hu := mem_FP_comp hr (cons_mem_FP bit)
  have hfalse := mem_FP_comp (mem_FP_comp hq (cons_mem_FP false)) normalize_mem_FP
  have htrue := mem_FP_comp (mem_FP_comp hq (cons_mem_FP true)) normalize_mem_FP
  have hcarry := (le_fppred hm hu).ite_mem_FP htrue hfalse
  have hzero : FPPred (fun p => Nat.fromBitsLE (pairFst (pairFst p)) = 0) :=
    (le_fppred hm (constFn_mem_FP [])).of_iff
    (fun p => by simp [Nat.fromBitsLE, Nat.fromBits])
  have h := hzero.ite_mem_FP (constFn_mem_FP []) hcarry
  refine mem_FP_of_eq h ?_
  intro p
  simp only [Function.comp_apply, divDigit]
  by_cases hz : Nat.fromBitsLE (pairFst (pairFst p)) = 0
  · simp only [hz, ↓reduceIte]
  · by_cases hc : Nat.fromBitsLE (pairFst (pairFst p)) ≤
        Nat.fromBitsLE (bit :: mod (pair (pairSnd p) (pairFst (pairFst p))))
    · simp only [hz, hc, decide_true, ↓reduceIte]
    · simp only [hz, hc, decide_false, ↓reduceIte]

/-- Input is `pair dividend divisor`; both words may be noncanonical. -/
def div (packet : List Bool) : List Bool := divFold (pairSnd packet) (pairFst packet)

theorem div_eq_bits (packet : List Bool) : div packet =
    (Nat.fromBitsLE (pairFst packet) / Nat.fromBitsLE (pairSnd packet)).bits :=
  divFold_eq_bits _ _

@[simp] theorem div_pair (a m : List Bool) :
    div (pair a m) = (Nat.fromBitsLE a / Nat.fromBitsLE m).bits := by
  simp only [div_eq_bits, pairFst_pair, pairSnd_pair]

theorem div_mem_FP : div ∈ FP := by
  refine recFold_mem_FP_of_bound (g := fun z t => divFold (pairSnd z) t)
    (divDigit_mem_FP false) (divDigit_mem_FP true) (constFn_mem_FP []) pairSnd_mem_FP pairFst_mem_FP
    (bound := id) ?_ ?_ ?_ PolyBound.id ?_
  · intro z; rfl
  · intro z t; simp only [divFold, pairFst_pair, pairSnd_pair]
  · intro z t; simp only [divFold, pairFst_pair, pairSnd_pair]
  · intro z t ht
    exact (divFold_length_le (pairSnd z) t).trans (ht.length_le.trans (pairFst_length_le z))

theorem div_length_le (a m : List Bool) : (div (pair a m)).length ≤ a.length := by
  simpa only [div, pairFst_pair, pairSnd_pair] using divFold_length_le m a

def divMod (packet : List Bool) : List Bool := pair (div packet) (mod packet)

theorem divMod_mem_FP : divMod ∈ FP := mem_FP_pair div_mem_FP mod_mem_FP

theorem divMod_pair (a m : List Bool) : divMod (pair a m) =
    pair (Nat.fromBitsLE a / Nat.fromBitsLE m).bits (Nat.fromBitsLE a % Nat.fromBitsLE m).bits := by
  simp only [divMod, div_pair, mod_pair]

theorem divMod_length_le (a m : List Bool) : (divMod (pair a m)).length ≤ 3 * a.length + 2 := by
  have hq := div_length_le a m
  have hr := mod_length_le a m
  simp only [divMod, pair_length]
  omega

end LeanCanny.Encoding.BinaryNat
