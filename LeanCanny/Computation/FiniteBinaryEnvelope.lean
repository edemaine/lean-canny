/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Common binary bounds for polynomially many indexed FP values

The output-length polynomial of an indexed binary reader gives a common
binary bound on its values at every index below a unary count. No maximum
computation or symbolic analysis of the reader is needed.
-/

@[expose] public section
namespace LeanCanny
open Turing.MultiTapeTM

/-- A finite family of binary FP values has a common binary FP envelope. -/
theorem BinaryFn.finiteEnvelope {f count : List Bool → ℕ} (hf : BinaryFn f) (hn : UnaryFn count) :
    ∃ g : List Bool → ℕ, BinaryFn g ∧
      ∀ c i, i < count c → f (pair c (BinaryNatCode.encode i)) ≤ g c := by
  obtain ⟨a, d, ha⟩ := hf.bits_mem_FP.polyBounded_length.exists_le
  have hsize : ∀ q, (f q).size ≤ a * (q.length + 1) ^ d := by
    intro q
    simpa only [encBits_apply, BinaryNatCode.length_encode] using ha q
  let width : List Bool → ℕ := fun c => a * (2 * c.length + count c + 3) ^ d
  have hw : UnaryFn width := (UnaryFn.const a).mul
    (((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add hn).add (UnaryFn.const 3)).pow_const d)
  refine ⟨fun c => 2 ^ width c, (BinaryFn.const 2).powUnary hw, ?_⟩
  intro c i hi
  have his : i.size ≤ i := Nat.size_le.mpr (show i < 2 ^ i from Nat.lt_two_pow_self)
  have hp : (pair c (BinaryNatCode.encode i)).length + 1 ≤ 2 * c.length + count c + 3 := by
    rw [pair_length, BinaryNatCode.length_encode]
    omega
  have hs := (hsize (pair c (BinaryNatCode.encode i))).trans
    (Nat.mul_le_mul_left a (Nat.pow_le_pow_left hp d))
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hs)

end LeanCanny
