/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryAddFP

/-!
# Polynomial-time binary multiplication

A shift-and-add fold reads the first operand from high to low. Every partial
product is normalized, and its bit length is at most the sum of the processed
operand length and the second operand length. This bounds all fold states,
rather than only the final output, and yields Complexitylib's machine-level FP
certificate. No magnitude is converted to a unary representation.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat
open Complexity

def mulFold (b : List Bool) : List Bool → List Bool
  | [] => []
  | false :: t => normalize (false :: mulFold b t)
  | true :: t => add (pair (false :: mulFold b t) b)

theorem mulFold_eq_bits (b t : List Bool) :
    mulFold b t = (Nat.fromBitsLE t * Nat.fromBitsLE b).bits := by
  induction t with
  | nil => simp [mulFold, Nat.fromBitsLE, Nat.fromBits]
  | cons bit t ih =>
      cases bit with
      | false =>
          simp only [mulFold, normalize_eq_bits, ih, Nat.fromBitsLE_cons, Nat.fromBitsLE_bits,
            Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_assoc]
      | true =>
          simp only [mulFold, add_pair, ih, Nat.fromBitsLE_cons, Nat.fromBitsLE_bits,
            Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          congr 1
          omega

theorem mulFold_length_le (b t : List Bool) :
    (mulFold b t).length ≤ t.length + b.length := by
  rw [mulFold_eq_bits, Nat.size_eq_bits_len, Nat.size_le, pow_add]
  calc
    _ ≤ Nat.fromBitsLE t * 2 ^ b.length :=
      Nat.mul_le_mul_left _ (Nat.fromBitsLE_lt_pow_length b).le
    _ < 2 ^ t.length * 2 ^ b.length :=
      Nat.mul_lt_mul_of_pos_right (Nat.fromBitsLE_lt_pow_length t) (pow_pos (by decide) _)

/-- Input: a self-delimiting pair of little-endian words. -/
def mul (packet : List Bool) : List Bool := mulFold (pairSnd packet) (pairFst packet)

theorem mul_eq_bits (packet : List Bool) : mul packet =
    (Nat.fromBitsLE (pairFst packet) * Nat.fromBitsLE (pairSnd packet)).bits :=
  mulFold_eq_bits _ _

@[simp] theorem mul_pair (a b : List Bool) :
    mul (pair a b) = (Nat.fromBitsLE a * Nat.fromBitsLE b).bits := by
  simp only [mul_eq_bits, pairFst_pair, pairSnd_pair]

theorem mul_mem_FP : mul ∈ FP := by
  have hprev := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hb := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hshift := mem_FP_comp hprev (Cobham.cons_mem_FP false)
  have hfalse := mem_FP_comp hshift normalize_mem_FP
  have htrue := mem_FP_comp (mem_FP_pair hshift hb) add_mem_FP
  refine recFold_mem_FP_of_bound (g := fun z t => mulFold (pairSnd z) t)
    hfalse htrue (constFn_mem_FP []) pairSnd_mem_FP pairFst_mem_FP
    (bound := fun n => 2 * n) ?_ ?_ ?_ ((PolyBound.const 2).mul PolyBound.id) ?_
  · intro z; rfl
  · intro z t; simp only [mulFold, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t; simp only [mulFold, pairFst_pair, pairSnd_pair, Function.comp_apply]
  · intro z t ht
    have hlen := mulFold_length_le (pairSnd z) t
    have ha := ht.length_le.trans (pairFst_length_le z)
    have hb := pairSnd_length_le z
    omega

theorem mul_length_le (a b : List Bool) : (mul (pair a b)).length ≤ a.length + b.length := by
  simpa only [mul, pairFst_pair, pairSnd_pair] using mulFold_length_le b a

/-- Input: `pair accumulator (pair leftFactor rightFactor)`. Reduction modulo
a runtime modulus is a separate operation. -/
def mulAdd (packet : List Bool) : List Bool := add (pair (pairFst packet) (mul (pairSnd packet)))

theorem mulAdd_eq_bits (packet : List Bool) : mulAdd packet =
    (Nat.fromBitsLE (pairFst packet) + Nat.fromBitsLE (pairFst (pairSnd packet)) *
      Nat.fromBitsLE (pairSnd (pairSnd packet))).bits := by
  rw [mulAdd, add_pair, mul_eq_bits, Nat.fromBitsLE_bits]

theorem mulAdd_mem_FP : mulAdd ∈ FP := by
  have hp := mem_FP_comp pairSnd_mem_FP mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair pairFst_mem_FP hp) add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

end LeanCanny.Encoding.BinaryNat
