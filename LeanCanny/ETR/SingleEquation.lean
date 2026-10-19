/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSize

/-!
# Normalizing the binary ETR language to a single equation

`normalize` is a total, executable map on all binary strings. Malformed strings map
to the unsatisfiable equation `1 = 0`. Correctness and a cubic output-length bound
are proved here. Membership of this map in Complexitylib's `FP` is a further
implementation obligation; a size bound alone does not prove polynomial time.
-/

@[expose] public section

namespace LeanCanny.ETR

@[simp] theorem Formula.not_satisfiable_eqZero_one :
    ¬ (Formula.eqZero (.const 1)).Satisfiable := by
  simp [Formula.Satisfiable, Formula.Holds, Term.eval]

namespace SingleEquation

/-- Canonically encoded, satisfiable, single integer polynomial equations over the reals. -/
def language : Set (List Bool) :=
  {bits | ∃ t : Term, bits = (Formula.eqZero t).encode ∧ (Formula.eqZero t).Satisfiable}

@[simp] theorem encode_mem_language (t : Term) :
    (Formula.eqZero t).encode ∈ language ↔ (Formula.eqZero t).Satisfiable := by
  constructor
  · rintro ⟨u, heq, hu⟩
    have ht := Formula.encode_injective heq
    cases ht
    exact hu
  · intro h
    exact ⟨t, rfl, h⟩

theorem language_subset_etr : language ⊆ ETR.language := by
  rintro bits ⟨t, rfl, ht⟩
  exact (ETR.encode_mem_language _).mpr ht

/-- Total normalization, including rejection of every malformed or noncanonical input. -/
def normalize (bits : List Bool) : List Bool :=
  match Formula.decode bits with
  | none => (Formula.eqZero (.const 1)).encode
  | some p => p.singleEquation.encode

/-- Every output is a well-formed single equation, even when the input is malformed. -/
theorem normalize_shape (bits : List Bool) :
    ∃ t : Term, normalize bits = (Formula.eqZero t).encode := by
  cases hd : Formula.decode bits with
  | none => exact ⟨.const 1, by simp [normalize, hd]⟩
  | some p => exact ⟨Term.sumSquares p.equationSystem.terms, by simp [normalize, hd, Formula.singleEquation]⟩

/-- The all-string normalization preserves exactly the yes-instances of ETR. -/
theorem mem_language_normalize_iff (bits : List Bool) :
    normalize bits ∈ language ↔ bits ∈ ETR.language := by
  cases hd : Formula.decode bits with
  | none =>
      have hn := not_mem_language_of_decode_none hd
      simp [normalize, hd, hn]
  | some p =>
      have hx := (Formula.decode_eq_some_iff bits p).mp hd
      rw [normalize, hd]
      change (Formula.eqZero (Term.sumSquares p.equationSystem.terms)).encode ∈ language ↔ _
      rw [encode_mem_language, hx, ETR.encode_mem_language]
      exact p.satisfiable_iff_singleEquation.symm

/-- A polynomial bound on literal output bits, for every binary input. -/
theorem normalize_length_le (bits : List Bool) :
    (normalize bits).length ≤ 500 * (bits.length + 1) ^ 3 := by
  cases hd : Formula.decode bits with
  | none =>
      have hlen : (Formula.eqZero (.const 1)).encode.length = 20 := by
        change (Formula.eqZero (.const 1)).inputSize = 20
        simp [Formula.inputSize_eq_dataSize, Formula.toData, Complexity.Data.cons_size,
          Codec.unary_size, Complexity.Data.size_empty]
      simp only [normalize, hd, hlen]
      nlinarith [Nat.zero_le bits.length, Nat.zero_le (bits.length ^ 2),
        Nat.zero_le (bits.length ^ 3)]
  | some p =>
      have hx := (Formula.decode_eq_some_iff bits p).mp hd
      simp only [normalize, hx, Formula.decode_encode]
      exact p.singleEquation_inputSize_le

end SingleEquation
end LeanCanny.ETR
