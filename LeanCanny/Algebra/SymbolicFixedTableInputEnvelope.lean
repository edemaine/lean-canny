/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.FiniteBinaryEnvelope

/-! # Common binary metadata on bounded-length symbolic source contexts

The number of possible leaf addresses need not be unary. Their encoded word
length suffices to bound every FP binary metadata output by one binary-FP
envelope. No finite maximum or enumeration is computed.
-/

@[expose] public section
namespace LeanCanny
open Turing.MultiTapeTM

theorem BinaryFn.inputEnvelope {f length : List Bool → ℕ} (hf : BinaryFn f) (hl : UnaryFn length) :
    ∃ g : List Bool → ℕ, BinaryFn g ∧ ∀ c q, q.length ≤ length c → f q ≤ g c := by
  obtain ⟨a, d, ha⟩ := hf.bits_mem_FP.polyBounded_length.exists_le
  have hsize : ∀ q, (f q).size ≤ a * (q.length + 1) ^ d := by
    intro q
    simpa only [encBits_apply, BinaryNatCode.length_encode] using ha q
  let width : List Bool → ℕ := fun c => a * (length c + 1) ^ d
  have hw : UnaryFn width := (UnaryFn.const a).mul ((hl.add (UnaryFn.const 1)).pow_const d)
  refine ⟨fun c => 2 ^ width c, (BinaryFn.const 2).powUnary hw, ?_⟩
  intro c q hq
  have hs := (hsize q).trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d))
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs)

/-- Binary metadata has a common unary bound on its bit length on every
bounded-length context; no maximum over contexts is evaluated. -/
theorem BinaryFn.inputSizeEnvelope {f length : List Bool → ℕ} (hf : BinaryFn f) (hl : UnaryFn length) :
    ∃ g : List Bool → ℕ, UnaryFn g ∧ ∀ c q, q.length ≤ length c → (f q).size ≤ g c := by
  obtain ⟨a, d, ha⟩ := hf.bits_mem_FP.polyBounded_length.exists_le
  refine ⟨fun c => a * (length c + 1) ^ d,
    (UnaryFn.const a).mul ((hl.add (UnaryFn.const 1)).pow_const d), ?_⟩
  intro c q hq
  have hs : (f q).size ≤ a * (q.length + 1) ^ d := by
    simpa only [encBits_apply, BinaryNatCode.length_encode] using ha q
  exact hs.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) d))

end LeanCanny
