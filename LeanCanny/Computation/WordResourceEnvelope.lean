/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.FiniteBinaryEnvelope

/-! # Native resource envelopes for all short task words

A polynomial word allowance bounds every binary FP value and every unary
FP value at all words within that allowance. The envelope follows from
the certified output-length polynomial, without enumerating task words.
-/

@[expose] public section
namespace LeanCanny
open Turing.MultiTapeTM

theorem BinaryFn.wordEnvelope {f B : List Bool → ℕ} (hf : BinaryFn f) (hB : UnaryFn B) :
    ∃ g : List Bool → ℕ, BinaryFn g ∧ ∀ r q, q.length ≤ B r → f q ≤ g r := by
  obtain ⟨a, d, ha⟩ := hf.bits_mem_FP.polyBounded_length.exists_le
  have hs : ∀ q, (f q).size ≤ a * (q.length + 1) ^ d := by
    intro q
    simpa only [encBits_apply, BinaryNatCode.length_encode] using ha q
  let width := fun r => a * (B r + 1) ^ d
  have hw : UnaryFn width := (UnaryFn.const a).mul ((hB.add (UnaryFn.const 1)).pow_const d)
  refine ⟨fun r => 2 ^ width r, (BinaryFn.const 2).powUnary hw, ?_⟩
  intro r q hq
  have H : (f q).size ≤ width r := (hs q).trans
    (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d))
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) H)

theorem UnaryFn.wordEnvelope {f B : List Bool → ℕ} (hf : UnaryFn f) (hB : UnaryFn B) :
    ∃ g : List Bool → ℕ, UnaryFn g ∧ ∀ r q, q.length ≤ B r → f q ≤ g r := by
  obtain ⟨a, d, ha⟩ := hf.polyBounded_length.exists_le
  have hs : ∀ q, f q ≤ a * (q.length + 1) ^ d := by
    intro q
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using ha q
  refine ⟨fun r => a * (B r + 1) ^ d,
    (UnaryFn.const a).mul ((hB.add (UnaryFn.const 1)).pow_const d), ?_⟩
  intro r q hq
  exact (hs q).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d))

end LeanCanny
