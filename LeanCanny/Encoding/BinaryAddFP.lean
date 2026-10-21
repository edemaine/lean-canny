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

theorem bump_length_le (bit : Bool) (bits : List Bool) :
    (bump bit bits).length ≤ bits.length + 1 := by
  cases bit
  · simp [bump]
  · exact increment_length_le bits

theorem bump_mem_FP {bits : List Bool → List Bool} (hbits : bits ∈ FP) (bit : Bool) :
    (fun z => bump bit (bits z)) ∈ FP := by
  cases bit
  · exact hbits
  · exact mem_FP_comp hbits increment_mem_FP

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

theorem addFold_length_le (a b t : List Bool) :
    (addFold a b t).length ≤ b.length + 3 * t.length := by
  induction t with
  | nil => simp only [addFold, List.length_drop, List.length_nil, mul_zero, Nat.add_zero]; omega
  | cons bit t ih =>
      have h1 := bump_length_le bit (false :: addFold a b t)
      have h2 := bump_length_le (b[a.length - (t.length + 1)]?.getD false)
        (bump bit (false :: addFold a b t))
      simp only [addFold, List.length_cons] at *
      omega

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

theorem addFold_mem_FP :
    (fun z => addFold (pairFst z) (pairSnd z) (pairFst z)) ∈ FP := by
  have hz := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have ht := pairSnd_mem_FP
  have ha := mem_FP_comp hz pairFst_mem_FP
  have hb := mem_FP_comp hz pairSnd_mem_FP
  have hi := (UnaryFn.length ha).sub ((UnaryFn.length ht).add (UnaryFn.const 1))
  have hbit := FPPred.getBit hb hi
  have hshift := mem_FP_comp hp (cons_mem_FP false)
  have stepFP : ∀ bit : Bool, (fun w =>
      bump ((pairSnd (pairFst (pairFst w)))[(pairFst (pairFst (pairFst w))).length -
        ((pairSnd w).length + 1)]?.getD false)
        (bump bit (false :: pairSnd (pairFst w)))) ∈ FP := by
    intro bit
    have hval := bump_mem_FP hshift bit
    have hinc := mem_FP_comp hval increment_mem_FP
    have h := hbit.ite_mem_FP hinc hval
    exact mem_FP_of_eq h (fun _ => rfl)
  have he := drop_mem_FP pairSnd_mem_FP (UnaryFn.length pairFst_mem_FP)
  refine recFold_mem_FP_of_bound
    (g := fun z t => addFold (pairFst z) (pairSnd z) t)
    (stepFP false) (stepFP true) he id_mem_FP pairFst_mem_FP
    (bound := fun n => 4 * n) ?_ ?_ ?_ ((PolyBound.const 4).mul PolyBound.id) ?_
  · intro z; rfl
  · intro z t; simp only [addFold, pairFst_pair, pairSnd_pair, id_eq]
  · intro z t; simp only [addFold, pairFst_pair, pairSnd_pair, id_eq]
  · intro z t ht
    have hlen := addFold_length_le (pairFst z) (pairSnd z) t
    have ha := ht.length_le.trans (pairFst_length_le z)
    have hb := pairSnd_length_le z
    omega

theorem add_mem_FP : add ∈ FP := mem_FP_comp addFold_mem_FP normalize_mem_FP

theorem add_length_le (a b : List Bool) : (add (pair a b)).length ≤ a.length + b.length + 1 := by
  rw [add_pair, Nat.size_eq_bits_len, Nat.size_le]
  have ha := (Nat.fromBitsLE_lt_pow_length a).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right a.length b.length))
  have hb := (Nat.fromBitsLE_lt_pow_length b).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left b.length a.length))
  rw [pow_succ]
  omega

end LeanCanny.Encoding.BinaryNat
