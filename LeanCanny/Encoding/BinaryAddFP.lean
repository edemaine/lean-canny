/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryNatFP

/-!
# Polynomial-time binary addition

Reading digit pairs from high to low, the next partial sum is twice the previous
one plus the two digits. Binary increment handles the carry. A bounded fold
therefore implements addition using bit strings throughout, including when the
input magnitudes are exponential in their bit lengths.

All input words are interpreted little endian. Outputs are canonical binary
codes, including for empty inputs and words with redundant high zeroes.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat


def bump (bit : Bool) (bits : List Bool) : List Bool := if bit then increment bits else bits

theorem bump_value (bit : Bool) (bits : List Bool) :
    Nat.fromBitsLE (bump bit bits) = Nat.fromBitsLE bits + (if bit then 1 else 0) := by
  cases bit <;> simp [bump, increment_value]

theorem value_drop (bits : List Bool) (n : ℕ) :
    Nat.fromBitsLE (bits.drop n) = (if bits[n]?.getD false then 1 else 0) +
      2 * Nat.fromBitsLE (bits.drop (n + 1)) := by
  have h : ∀ word : List Bool, Nat.fromBitsLE word =
      (if word[0]?.getD false then 1 else 0) + 2 * Nat.fromBitsLE (word.drop 1) := by
    intro word
    cases word with
    | nil => rfl
    | cons b t => simpa using Nat.fromBitsLE_cons b t
  simpa only [List.getElem?_drop, Nat.add_zero, List.drop_drop] using h (bits.drop n)

/-- The first argument fixes the input width and the second supplies its other
operand. The final argument is the suffix currently processed by the fold. -/
def addFold (a b : List Bool) : List Bool → List Bool
  | [] => b.drop a.length
  | bit :: t =>
      bump (b[a.length - (t.length + 1)]?.getD false)
        (bump bit (false :: addFold a b t))

theorem addFold_value (a b t : List Bool) (n : ℕ) (hn : n + t.length = a.length) :
    Nat.fromBitsLE (addFold a b t) = Nat.fromBitsLE t + Nat.fromBitsLE (b.drop n) := by
  induction t generalizing n with
  | nil =>
      have he : n = a.length := by simpa using hn
      subst n
      simp [addFold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit t ih =>
      have hi : a.length - (t.length + 1) = n := by simp only [List.length_cons] at hn; omega
      have ht : n + 1 + t.length = a.length := by simp only [List.length_cons] at hn; omega
      rw [addFold, bump_value, bump_value, Nat.fromBitsLE_cons, ih (n + 1) ht,
        Nat.fromBitsLE_cons, value_drop b n, hi]
      cases bit <;> cases b[n]?.getD false <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The input is a self-delimiting pair of little-endian binary words. -/
def add (packet : List Bool) : List Bool :=
  normalize (addFold (pairFst packet) (pairSnd packet) (pairFst packet))

theorem add_eq_bits (packet : List Bool) : add packet =
    (Nat.fromBitsLE (pairFst packet) + Nat.fromBitsLE (pairSnd packet)).bits := by
  rw [add, normalize_eq_bits, addFold_value _ _ _ 0 (by simp), List.drop_zero]

@[simp] theorem add_pair (a b : List Bool) :
    add (pair a b) = (Nat.fromBitsLE a + Nat.fromBitsLE b).bits := by
  simp only [add_eq_bits, pairFst_pair, pairSnd_pair]

theorem add_mem_FP : add ∈ FP := by
  have h := natBits_computable.comp
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_add'
      (fromBitsLE_computable.comp pairFst_mem_FP) (fromBitsLE_computable.comp pairSnd_mem_FP))
  exact mem_FP_of_eq h (fun p => (add_eq_bits p).symm)

theorem add_length_le (a b : List Bool) : (add (pair a b)).length ≤ a.length + b.length + 1 := by
  rw [add_pair, Nat.size_eq_bits_len, Nat.size_le]
  have ha := (Nat.fromBitsLE_lt_pow_length a).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right a.length b.length))
  have hb := (Nat.fromBitsLE_lt_pow_length b).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left b.length a.length))
  rw [pow_succ]
  omega

end LeanCanny.Encoding.BinaryNat
