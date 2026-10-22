/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskStorage
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Common metadata bounds from native FP controls

The determinant and moment storage profiles count binary field lengths.
Their unary values are polynomial-time computable even when the fields
themselves are exponentially large. A common task-word bound therefore
supplies a common polynomial metadata bound without further assumptions.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM

private theorem binary_size_unary {f : List Bool → ℕ} (hf : BinaryFn f) :
    UnaryFn (fun z => (f z).size) :=
  (UnaryFn.length hf.bits_mem_FP).of_eq (fun z => Nat.size_eq_bits_len (f z))

theorem determinantFields_unary {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    UnaryFn (determinantFields (F := F)) := by
  have hn := BinaryFn.of_bits (mem_FP_of_eq ha.dimension a.dimension_eq)
  have hd := BinaryFn.of_bits (mem_FP_of_eq ha.degree a.degree_eq)
  have hm := BinaryFn.of_bits (mem_FP_of_eq ha.modulus a.modulus_eq)
  exact ((binary_size_unary (((hn.add (BinaryFn.const 1)).mul (hn.add (BinaryFn.const 1))).mul
    (hd.add (BinaryFn.const 1)))).add (binary_size_unary hn)).add (binary_size_unary hm)

theorem momentFields_unary {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    UnaryFn (momentFields (F := F)) := by
  have hc := a.moment_controls ha
  have hn := BinaryFn.of_bits (mem_FP_of_eq hc.dimension a.momentAccess.dimension_eq)
  have hd := BinaryFn.of_bits (mem_FP_of_eq hc.degree a.momentAccess.degree_eq)
  have he := BinaryFn.of_bits (mem_FP_of_eq hc.exponent a.momentAccess.exponent_eq)
  have hm := BinaryFn.of_bits (mem_FP_of_eq hc.modulus a.momentAccess.modulus_eq)
  exact ((binary_size_unary ((hn.add (BinaryFn.const 2)).mul (hd.add (BinaryFn.const 1)))).add
    (binary_size_unary (he.add (BinaryFn.const 2)))).add (binary_size_unary hm)

/-- One native unary bound controls both profiles on every word of bounded
length. This uses only the FP controls, not source coefficient certificates. -/
theorem commonMetadata_bound {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (K : List Bool → ℕ) (hK : UnaryFn K) :
    ∃ M : List Bool → ℕ, UnaryFn M ∧ ∀ root p, p.length ≤ K root →
      determinantFields (F := F) p ≤ M root ∧ momentFields (F := F) p ≤ M root := by
  have hf := (determinantFields_unary a ha).add (momentFields_unary a ha)
  obtain ⟨c, d, h⟩ := hf.polyBounded_length.exists_le
  refine ⟨fun root => c * (K root + 1) ^ d,
    (UnaryFn.const c).mul ((hK.add (UnaryFn.const 1)).pow_const d), ?_⟩
  intro root p hp
  have hb : determinantFields (F := F) p + momentFields (F := F) p ≤ c * (p.length + 1) ^ d := by
    simpa only [encUnary_apply, List.length_replicate, encBits_apply] using h p
  have hm := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) d)
  dsimp only
  constructor <;> omega

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
