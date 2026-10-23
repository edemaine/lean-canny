/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinarySubFP
public import LeanCanny.Encoding.BinaryMulFP

/-!
# Polynomial-time binary modular reduction

Binary long division reads the dividend from high to low. A doubled remainder
plus the next digit is below twice a positive modulus, so one comparison and
one subtraction suffice at each step. All intermediate remainders are canonical
and no longer than the processed dividend. The zero-modulus case follows Nat's
convention `a % 0 = a` and is included in the FP certificate.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat


def reduceOnce (packet : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd packet) ≤ Nat.fromBitsLE (pairFst packet) then sub packet
  else normalize (pairFst packet)

theorem reduceOnce_pair (a m : List Bool) : reduceOnce (pair a m) =
    (if Nat.fromBitsLE m ≤ Nat.fromBitsLE a then Nat.fromBitsLE a - Nat.fromBitsLE m
      else Nat.fromBitsLE a).bits := by
  simp only [reduceOnce, pairFst_pair, pairSnd_pair]
  split_ifs <;> simp only [sub_pair, normalize_eq_bits]

theorem reduceOnce_mem_FP : reduceOnce ∈ FP := by
  have hnorm := mem_FP_comp pairFst_mem_FP normalize_mem_FP
  have h := ge_fppred.ite_mem_FP sub_mem_FP hnorm
  exact mem_FP_of_eq h (fun _ => rfl)

theorem subtract_once_mod (m u : ℕ) (hu : u < 2 * m) :
    (if m ≤ u then u - m else u) = u % m := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : u - m < m)]
  · rw [Nat.mod_eq_of_lt (by omega : u < m)]

theorem remainder_step (m t : ℕ) (bit : Bool) :
    (if m ≤ (if bit then 1 else 0) + 2 * (t % m) then
        (if bit then 1 else 0) + 2 * (t % m) - m
      else (if bit then 1 else 0) + 2 * (t % m)) =
        ((if bit then 1 else 0) + 2 * t) % m := by
  by_cases hm : m = 0
  · simp [hm]
  · have hr := Nat.mod_lt t (by omega : 0 < m)
    have hu : (if bit then 1 else 0) + 2 * (t % m) < 2 * m := by
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [subtract_once_mod m _ hu]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

def modFold (m : List Bool) : List Bool → List Bool
  | [] => []
  | bit :: t => reduceOnce (pair (bit :: modFold m t) m)

theorem modFold_eq_bits (m t : List Bool) :
    modFold m t = (Nat.fromBitsLE t % Nat.fromBitsLE m).bits := by
  induction t with
  | nil => simp [modFold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit t ih =>
      rw [modFold, reduceOnce_pair, ih, Nat.fromBitsLE_cons, Nat.fromBitsLE_bits,
        Nat.fromBitsLE_cons, remainder_step]

theorem modFold_length_le (m t : List Bool) : (modFold m t).length ≤ t.length := by
  rw [modFold_eq_bits, Nat.size_eq_bits_len]
  exact (Nat.size_le_size (Nat.mod_le _ _)).trans
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length t))

/-- Input: `pair binaryDividend binaryModulus`. -/
def mod (packet : List Bool) : List Bool := modFold (pairSnd packet) (pairFst packet)

theorem mod_eq_bits (packet : List Bool) : mod packet =
    (Nat.fromBitsLE (pairFst packet) % Nat.fromBitsLE (pairSnd packet)).bits :=
  modFold_eq_bits _ _

@[simp] theorem mod_pair (a m : List Bool) :
    mod (pair a m) = (Nat.fromBitsLE a % Nat.fromBitsLE m).bits := by
  simp only [mod_eq_bits, pairFst_pair, pairSnd_pair]

theorem mod_mem_FP : mod ∈ FP := by
  let step := fun m acc bit => reduceOnce (pair (bit :: acc) m)
  have hstep : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => step p.1.1 p.1.2 p.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by
    exact reduceOnce_mem_FP.comp (by fun_prop)
  refine foldrEncodedWith_spec id (step := step) (g := fun z t => modFold (pairSnd z) t)
    pairSnd_mem_FP pairFst_mem_FP (constFn_mem_FP []) hstep
    (fun _ _ _ => rfl) (PolyBound.id.polyBounded (fun z : List Bool => z.length)) ?_
  intro z t ht
  exact (modFold_length_le (pairSnd z) t).trans (ht.length_le.trans (pairFst_length_le z))

theorem mod_length_le (a m : List Bool) : (mod (pair a m)).length ≤ a.length := by
  simpa only [mod, pairFst_pair, pairSnd_pair] using modFold_length_le m a

/-- Input: `pair modulus (pair accumulator (pair leftFactor rightFactor))`. -/
def mulAddMod (packet : List Bool) : List Bool :=
  mod (pair (mulAdd (pairSnd packet)) (pairFst packet))

theorem mulAddMod_eq_bits (packet : List Bool) : mulAddMod packet =
    ((Nat.fromBitsLE (pairFst (pairSnd packet)) +
      Nat.fromBitsLE (pairFst (pairSnd (pairSnd packet))) *
        Nat.fromBitsLE (pairSnd (pairSnd (pairSnd packet)))) %
      Nat.fromBitsLE (pairFst packet)).bits := by
  rw [mulAddMod, mod_pair, mulAdd_eq_bits, Nat.fromBitsLE_bits]

theorem mulAddMod_mem_FP : mulAddMod ∈ FP := by
  have hval := mem_FP_comp pairSnd_mem_FP mulAdd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hval pairFst_mem_FP) mod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

end LeanCanny.Encoding.BinaryNat
