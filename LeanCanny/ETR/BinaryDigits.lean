/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EncodingFP

/-!
# Recognizing canonical binary magnitudes without unary expansion

An integer constant can have exponentially large magnitude relative to its input
length. Its digit list is therefore checked directly: the empty word represents
zero, and every nonempty little-endian canonical word ends in `true`.
-/

@[expose] public section

namespace LeanCanny.ETR.Codec


def CanonicalDigits (bits : List Bool) : Prop := bits = [] ∨ bits.getLast? = some true

instance canonicalDigitsDecidable (bits : List Bool) : Decidable (CanonicalDigits bits) := by
  unfold CanonicalDigits
  infer_instance

theorem canonicalDigits_bits (n : ℕ) : CanonicalDigits n.bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [CanonicalDigits]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      by_cases hz : n = 0
      · subst n
        simp [CanonicalDigits, hn rfl]
      · have hbits : n.bits ≠ [] := by
          intro hb
          apply hz
          have he := Nat.fromBitsLE_bits n
          rw [hb] at he
          simpa [Nat.fromBitsLE, Nat.fromBits] using he.symm
        right
        rw [List.getLast?_cons_of_ne_nil hbits]
        exact ih.resolve_left hbits

theorem canonicalDigits_iff (bits : List Bool) :
    CanonicalDigits bits ↔ ∃ n : ℕ, bits = n.bits := by
  constructor
  · intro h
    induction bits with
    | nil => exact ⟨0, by simp⟩
    | cons b bs ih =>
        cases bs with
        | nil =>
            have hb : b = true := by simpa [CanonicalDigits] using h
            subst b
            exact ⟨1, by simp⟩
        | cons c cs =>
            have ht : CanonicalDigits (c :: cs) := by simpa [CanonicalDigits] using h
            obtain ⟨n, hn⟩ := ih ht
            have hn0 : n ≠ 0 := by intro hz; subst n; simp at hn
            refine ⟨Nat.bit b n, ?_⟩
            rw [Nat.bits_append_bit n b (fun hz => False.elim (hn0 hz)), ← hn]
  · rintro ⟨n, rfl⟩
    exact canonicalDigits_bits n

theorem lastBit_true_iff (bits : List Bool) :
    bits[bits.length - 1]?.getD false = true ↔ bits.getLast? = some true := by
  rw [← List.getLast?_eq_getElem?]
  cases hb : bits.getLast? with
  | none => simp
  | some b => cases b <;> simp

theorem canonicalDigits_fppred : FPPred CanonicalDigits := by
  have hempty := FPPred.eq (UnaryFn.length id_mem_FP) (UnaryFn.const 0)
  have hlast := FPPred.getBit id_mem_FP ((UnaryFn.length id_mem_FP).sub (UnaryFn.const 1))
  refine (hempty.or hlast).of_iff fun bits => ?_
  simp only [id_eq, lastBit_true_iff, List.length_eq_zero_iff, CanonicalDigits]

end LeanCanny.ETR.Codec
