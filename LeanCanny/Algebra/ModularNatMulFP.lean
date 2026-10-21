/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularPowFP

/-! # Modular multiplication by an unreduced binary natural -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ArithmeticBits

open LeanCanny.Encoding

theorem mulMod_nat_residueBits (m : ℕ) (x : ZMod m) (n : ℕ) :
    BinaryNat.mulMod (pair (BinaryNatCode.encode m) (pair (residueBits x) (BinaryNatCode.encode n))) =
      residueBits (x * (n : ZMod m)) := by
  simp only [BinaryNat.mulMod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod]

end LeanCanny.Algebra.MatrixPower.ArithmeticBits
