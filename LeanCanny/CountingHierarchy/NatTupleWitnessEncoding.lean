/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.NativeBinaryBounds
public import LeanCanny.CountingHierarchy.Controlled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-! # Fixed polynomial-width witnesses for bounded tuples of binary naturals -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

abbrev encNatTuple : List ℕ ↪ List Bool := encList encNat

def natTupleWord (word : List Bool) : List ℕ :=
  ((Decoder.pair (Decoder.list Decoder.nat) Decoder.bits).decode word).1

theorem natTupleWord_polyTime : ComputableInPolyTime natTupleWord encBits encNatTuple :=
  (ComputableInPolyTime.fst encNatTuple encBits).comp
    (Decoder.pair (Decoder.list Decoder.nat) Decoder.bits).computableInPolyTime

def natTupleCodeLengthBound (M N : ℕ) : ℕ := N * (2 * M.size + 1)

def natTupleWitnessWidth (M N : ℕ) : ℕ := 2 * natTupleCodeLengthBound M N + 1

theorem natTupleWord_encoded (data : List ℕ) (padding : List Bool) :
    natTupleWord (encPair encNatTuple encBits (data, padding)) = data := by
  rw [natTupleWord, Decoder.decode_enc]

theorem natTuple_length_le (M N : ℕ) (data : List ℕ) (hN : data.length ≤ N)
    (hM : ∀ i ∈ data, i ≤ M) : (encNatTuple data).length ≤ natTupleCodeLengthBound M N := by
  have hentry (i : ℕ) (hi : i ∈ data) : (encNat i).length ≤ M.size := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size (hM i hi)
  exact (length_encList_le encNat data hentry).trans (Nat.mul_le_mul_right _ hN)

theorem exists_natTupleWord (M N : ℕ) (data : List ℕ) (hN : data.length ≤ N)
    (hM : ∀ i ∈ data, i ≤ M) :
    ∃ word : List Bool, word.length = natTupleWitnessWidth M N ∧ natTupleWord word = data := by
  let codeLength := (encNatTuple data).length
  let padding := List.replicate (natTupleWitnessWidth M N - (2 * codeLength + 1)) false
  refine ⟨encPair encNatTuple encBits (data, padding), ?_, natTupleWord_encoded _ _⟩
  have hb : codeLength ≤ natTupleCodeLengthBound M N := natTuple_length_le M N data hN hM
  rw [length_encPair]
  change 2 * codeLength + 1 + padding.length = natTupleWitnessWidth M N
  simp only [padding, List.length_replicate]
  have hwidth : 2 * codeLength + 1 ≤ natTupleWitnessWidth M N := by
    unfold natTupleWitnessWidth
    omega
  omega

@[fun_prop] theorem natTupleWitnessWidth_polyTime {α : Type} {enc : α ↪ List Bool} {M N : α → ℕ}
    (hM : ComputableInPolyTime M enc encNat) (hN : ComputableInPolyTime N enc encUnary) :
    ComputableInPolyTime (fun w => natTupleWitnessWidth (M w) (N w)) enc encUnary := by
  have hs := ComputableInPolyTime.binary_size.comp hM
  have hentry := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (.const 2) hs) (.const 1)
  exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2)
    (ComputableInPolyTime.unary_mul' hN hentry)) (.const 1)

end LeanCanny.CountingHierarchy
