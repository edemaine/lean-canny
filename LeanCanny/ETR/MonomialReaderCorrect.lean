/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderEncoding

/-! # Exact simulation of the selected-monomial stack controller -/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

theorem encoded_pair_ne_nil (a b : List Bool) : pair a b ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp only [pair_length, List.length_nil] at hh
  omega

theorem stepBits_encode {R : Type*} [Monoid R] (code : R → List Bool)
    (constant : ℤ → R) (variableValue : ℕ → R) (atom : List Bool → List Bool) (c : List Bool)
    (hc : ∀ z v, atom (pair c (pair (Term.const z).toData.toBits (code v))) = code (v * constant z))
    (hv : ∀ i v, atom (pair c (pair (Term.var i).toData.toBits (code v))) = code (v * variableValue i)) (s : State R) :
    stepBits atom (pair c (s.encode code)) = pair c ((step constant variableValue s).encode code) := by
  simp [Term.toData, Codec.unary] at hc hv
  rcases s with ⟨todo, v⟩
  cases todo with
  | nil => simp [stepBits, todoBits, State.encode, DynamicTreeFold.stackBits, step]
  | cons q rest =>
    rcases q with ⟨t, r⟩
    cases t <;>
      simp [stepBits, todoBits, accumulator, headTask, termBits, indexBits, restBits,
        leftTerm, rightTerm, leftCount, rightCount, leftTasks, rightTasks, productTasks, atomQuery, emit,
        State.encode, Task.encode, DynamicTreeFold.stackBits, encoded_pair_ne_nil, step,
        NNF.hasTwo_toBits, NNF.two, NNF.second, NNF.third, Term.toData, Codec.unary,
        MonomialCount.read_term, BinaryNat.normalize_bits, BinaryNat.sub_pair, BinaryNat.div_pair, BinaryNat.mod_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, apply_ite, hc, hv]

theorem iterate_encode {R : Type*} [Monoid R] (code : R → List Bool)
    (constant : ℤ → R) (variableValue : ℕ → R) (atom : List Bool → List Bool) (c : List Bool)
    (hc : ∀ z v, atom (pair c (pair (Term.const z).toData.toBits (code v))) = code (v * constant z))
    (hv : ∀ i v, atom (pair c (pair (Term.var i).toData.toBits (code v))) = code (v * variableValue i))
    (s : State R) (k : ℕ) :
    (stepBits atom)^[k] (pair c (s.encode code)) = pair c (((step constant variableValue)^[k] s).encode code) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepBits_encode code constant variableValue atom c hc hv,
      Function.iterate_succ_apply']

end LeanCanny.ETR.MonomialReader
