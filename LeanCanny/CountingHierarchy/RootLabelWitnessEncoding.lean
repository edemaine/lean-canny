/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CodedCriticalCriterion
public import LeanCanny.CountingHierarchy.NativeBinaryBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Polynomial-width bit witnesses for bounded root labels and shifts -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

abbrev encRootLabelWitness : (List (ℕ × ℕ) × ℕ) ↪ List Bool := encPair encRootLabelCode encNat

@[expose] def rootLabelCodeLengthBound (D N : ℕ) : ℕ := 2 * (N * (4 * D.size + 7)) + 1 + D.size

@[expose] def rootLabelWitnessWidth (D N : ℕ) : ℕ := 2 * rootLabelCodeLengthBound D N + 1

@[expose] def rootLabelWitnessDecoder : Decoder encRootLabelWitness :=
  Decoder.pair (Decoder.list (Decoder.pair Decoder.nat Decoder.nat)) Decoder.nat

/-- An outer frame permits arbitrary padding after a complete witness. -/
@[expose] def rootLabelWordWitness (word : List Bool) : List (ℕ × ℕ) × ℕ :=
  ((Decoder.pair rootLabelWitnessDecoder Decoder.bits).decode word).1

theorem rootLabelWordWitness_polyTime :
    ComputableInPolyTime rootLabelWordWitness encBits encRootLabelWitness :=
  (ComputableInPolyTime.fst encRootLabelWitness encBits).comp
    (Decoder.pair rootLabelWitnessDecoder Decoder.bits).computableInPolyTime

theorem rootLabelWordWitness_encoded (data : List (ℕ × ℕ)) (e : ℕ) (padding : List Bool) :
    rootLabelWordWitness (encPair encRootLabelWitness encBits ((data, e), padding)) = (data, e) := by
  rw [rootLabelWordWitness, Decoder.decode_enc]

theorem rootLabelWitness_length_le {D N e : ℕ} {data : List (ℕ × ℕ)}
    (hdata : RootLabelCodeBound D N data) (he : e ≤ D) :
    (encRootLabelWitness (data, e)).length ≤ rootLabelCodeLengthBound D N := by
  have hpair (t : ℕ × ℕ) (ht : t ∈ data) :
      (encPair encNat encNat t).length ≤ 2 * D.size + 3 := by
    have hindex := Nat.size_le_size (hdata.2 t ht).1.le
    have hsign : t.2.size ≤ 2 := by
      have h := Nat.size_le_size (Nat.le_of_lt (hdata.2 t ht).2)
      exact h
    simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len]
    omega
  have hlist := length_encList_le (encPair encNat encNat) data (b := 2 * D.size + 3) hpair
  have hlen : (encRootLabelCode data).length ≤ N * (4 * D.size + 7) := by
    have hcount := Nat.mul_le_mul_right (2 * (2 * D.size + 3) + 1) hdata.1
    nlinarith
  have hshift := Nat.size_le_size he
  simp only [encRootLabelWitness, length_encPair, encNat_apply, Nat.size_eq_bits_len,
    rootLabelCodeLengthBound]
  omega

/-- Every bounded code has a padded word of one fixed polynomial width. -/
theorem exists_rootLabelWordWitness {D N e : ℕ} {data : List (ℕ × ℕ)}
    (hdata : RootLabelCodeBound D N data) (he : e ≤ D) :
    ∃ word : List Bool, word.length = rootLabelWitnessWidth D N ∧
      rootLabelWordWitness word = (data, e) := by
  let codeLength := (encRootLabelWitness (data, e)).length
  let padding := List.replicate (rootLabelWitnessWidth D N - (2 * codeLength + 1)) false
  refine ⟨encPair encRootLabelWitness encBits ((data, e), padding), ?_, rootLabelWordWitness_encoded _ _ _⟩
  have hb := rootLabelWitness_length_le hdata he
  change codeLength ≤ rootLabelCodeLengthBound D N at hb
  rw [length_encPair]
  change 2 * codeLength + 1 + padding.length = rootLabelWitnessWidth D N
  simp only [padding, List.length_replicate]
  have hwidth : 2 * codeLength + 1 ≤ rootLabelWitnessWidth D N := by
    unfold rootLabelWitnessWidth
    omega
  omega

theorem rootLabelWitnessWidth_polyTime {α : Type} {enc : α ↪ List Bool} {D N : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hN : ComputableInPolyTime N enc encUnary) :
    ComputableInPolyTime (fun w => rootLabelWitnessWidth (D w) (N w)) enc encUnary := by
  have hsize := ComputableInPolyTime.binary_size.comp hD
  have hentry := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (.const 4) hsize) (.const 7)
  have hcode := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2)
      (ComputableInPolyTime.unary_mul' hN hentry)) (.const 1)) hsize
  exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (.const 2) hcode) (.const 1)

end LeanCanny.CountingHierarchy
