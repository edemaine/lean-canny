/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularNegFP

/-! # FP addition of canonical residues

The binary modulus is positive in the residue specification. The FP routine
is total on all words and includes modulus one.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ArithmeticBits

open LeanCanny.Encoding

def addMod (p : List Bool) : List Bool :=
  BinaryNat.mod (pair (BinaryNat.add (pair (pairFst (pairSnd p)) (pairSnd (pairSnd p)))) (pairFst p))

theorem addMod_mem_FP : addMod ∈ FP := by
  have hx := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hy := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have ha := mem_FP_comp (mem_FP_pair hx hy) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair ha pairFst_mem_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem addMod_residueBits (m : ℕ) [NeZero m] (x y : ZMod m) :
    addMod (pair (BinaryNatCode.encode m) (pair (residueBits x) (residueBits y))) = residueBits (x + y) := by
  simp only [addMod, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair, BinaryNat.add_pair,
    residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_add]

end LeanCanny.Algebra.MatrixPower.ArithmeticBits
