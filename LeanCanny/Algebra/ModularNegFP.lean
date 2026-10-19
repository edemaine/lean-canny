/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-!
# Certified binary negation of residues

Input is a paired binary modulus and value. Reducing the value, subtracting
it from the modulus, and reducing again gives the canonical negated residue.
The routine is FP on all words and agrees with ZMod negation for a nonzero
modulus, including modulus one.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ArithmeticBits
open Complexity
open LeanCanny.Encoding

def negate (p : List Bool) : List Bool :=
  let m := pairFst p
  let x := BinaryNat.mod (pair (pairSnd p) m)
  BinaryNat.mod (pair (BinaryNat.sub (pair m x)) m)

theorem negate_mem_FP : negate ∈ FP := by
  have hx := mem_FP_comp (mem_FP_pair pairSnd_mem_FP pairFst_mem_FP) BinaryNat.mod_mem_FP
  have hs := mem_FP_comp (mem_FP_pair pairFst_mem_FP hx) BinaryNat.sub_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs pairFst_mem_FP) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := negate) h ?_
  intro p
  simp only [Function.comp_apply, negate]

theorem negate_pair (m x : List Bool) :
    negate (pair m x) = ((Nat.fromBitsLE m - Nat.fromBitsLE x % Nat.fromBitsLE m) %
      Nat.fromBitsLE m).bits := by
  simp only [negate, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair, BinaryNat.sub_pair,
    Nat.fromBitsLE_bits]

theorem negate_residueBits (m : ℕ) [NeZero m] (x : ZMod m) :
    negate (pair (BinaryNatCode.encode m) (residueBits x)) = residueBits (-x) := by
  simp only [negate_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.mod_eq_of_lt (ZMod.val_lt x), ZMod.neg_val']

end LeanCanny.Algebra.MatrixPower.ArithmeticBits
