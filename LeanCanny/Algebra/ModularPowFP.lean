/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryPowModFP
public import LeanCanny.Algebra.ModularNegFP

/-!
# Binary products and powers agree with residue arithmetic

The base of a power may already be a residue or an unreduced natural. The
positive-modulus protocol includes modulus one and arbitrary composite moduli.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ArithmeticBits

open LeanCanny.Encoding

theorem mulMod_residueBits (m : ℕ) (x y : ZMod m) :
    BinaryNat.mulMod (pair (BinaryNatCode.encode m) (pair (residueBits x) (residueBits y))) =
      residueBits (x * y) := by
  simp only [BinaryNat.mulMod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ZMod.val_mul]

theorem negate_nat (m : ℕ) [NeZero m] (c : ℕ) :
    negate (pair (BinaryNatCode.encode m) (BinaryNatCode.encode c)) =
      residueBits (-(c : ZMod m)) := by
  simp only [negate_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ZMod.neg_val', ZMod.val_natCast]

theorem powMod_residueBits (b e : List Bool) (x : ZMod (Nat.fromBitsLE b + 1)) :
    BinaryNat.powMod (pair (residueBits x)
      (pair e b)) = residueBits (x ^ Nat.fromBitsLE e) := by
  have hx : ((x.val ^ Nat.fromBitsLE e : ℕ) : ZMod (Nat.fromBitsLE b + 1)) =
      x ^ Nat.fromBitsLE e := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [← hx]
  simp only [BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair, residueBits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast]

end LeanCanny.Algebra.MatrixPower.ArithmeticBits
