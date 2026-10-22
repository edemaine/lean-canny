/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerEncoding
public import LeanCanny.Encoding.BinaryModFP

/-!
# Certified scalar arithmetic for modular matrix powering

The modulus is a binary input field, rather than a fixed constant in the
machine. A uniform FP routine computes `acc + lhs*rhs` modulo that field and
agrees with the residue encoding of the corresponding ZMod operation for every
nonzero modulus. The encoded one also handles modulus one, where it equals zero.

`MatrixPowerController` assembles the full control transition with these scalar
callbacks. Matrix-entry access must also be supplied with an FP certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ArithmeticBits

open LeanCanny.Encoding

/-- Input: `pair modulus (pair accumulator (pair leftFactor rightFactor))`. -/
def combine : List Bool → List Bool := BinaryNat.mulAddMod

theorem combine_mem_FP : combine ∈ FP := BinaryNat.mulAddMod_mem_FP

theorem combine_residueBits (m : ℕ) [NeZero m] (acc lhs rhs : ZMod m) :
    combine (pair (BinaryNatCode.encode m)
      (pair (residueBits acc) (pair (residueBits lhs) (residueBits rhs)))) =
        residueBits (acc + lhs * rhs) := by
  simp only [combine, BinaryNat.mulAddMod_eq_bits, pairFst_pair, pairSnd_pair,
    residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_add, ZMod.val_mul]
  congr 1
  simp only [Nat.add_mod, Nat.mod_mod]

def zero (_ : List Bool) : List Bool := []

theorem zero_mem_FP : zero ∈ FP := constFn_mem_FP []

theorem zero_residueBits (m : ℕ) : zero (BinaryNatCode.encode m) = residueBits (0 : ZMod m) := by
  simp [zero, residueBits, BinaryNatCode.encode]

def one (modulus : List Bool) : List Bool := BinaryNat.mod (pair [true] modulus)

theorem one_mem_FP : one ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (constFn_mem_FP [true]) id_mem_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem one_residueBits (m : ℕ) : one (BinaryNatCode.encode m) = residueBits (1 : ZMod m) := by
  rw [one, BinaryNat.mod_pair]
  simp only [BinaryNatCode.encode, residueBits, Nat.fromBitsLE_bits, ZMod.val_one_eq_one_mod]
  rfl

end LeanCanny.Algebra.MatrixPower.ArithmeticBits
