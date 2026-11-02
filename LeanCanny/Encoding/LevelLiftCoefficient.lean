/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FixedLeadingDilationValueBound
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace

/-! # Native residues of the original-height level coefficient

The integer A need not be serialized. Its original-height exponent is binary;
modular repeated squaring writes its residue directly for every positive query
modulus, including composite moduli.
-/
@[expose] public section
namespace LeanCanny.Encoding.LevelLiftCoefficient
open LeanCanny.Algebra.MatrixPower LeanCanny.Geometry.FixedLeadingDilationValueBound

def exponent (n D G : List Bool → ℕ) (c : List Bool) : ℕ :=
  (n c).size+G c*LeanCanny.Algebra.FixedLeadingTiltedSource.degree (D c)+2

theorem exponent_binary {n D G : List Bool → ℕ} (hn : UnaryFn n) (hD : UnaryFn D) (hG : BinaryFn G) :
    BinaryFn (exponent n D G) :=
  (((BinaryFn.ofUnary hn).size).add (hG.mul (((BinaryFn.const 4).mul (BinaryFn.ofUnary hD)).add (BinaryFn.const 2)))).add (BinaryFn.const 2)

def read (n D G : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.powMod (pair (BinaryNatCode.encode 2) (pair (BinaryNatCode.encode (exponent n D G c)) (modulus c)))

theorem read_FP {n D G : List Bool → ℕ} {modulus : List Bool → List Bool}
    (hn : UnaryFn n) (hD : UnaryFn D) (hG : BinaryFn G) (hm : modulus ∈ FP) : read n D G modulus ∈ FP :=
  mem_FP_comp (mem_FP_pair (constFn_mem_FP _) (mem_FP_pair (exponent_binary hn hD hG).bits_mem_FP hm)) BinaryNat.powMod_mem_FP

theorem read_value (n D G : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) :
    read n D G modulus c = residueBits
      ((levelCoefficient (n c) (D c) (G c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  let m := Nat.fromBitsLE (modulus c)+1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have HE : ((levelCoefficient (n c) (D c) (G c) : ℤ) : ZMod m) =
      ((2^exponent n D G c : ℕ) : ZMod m) := by
    simp only [levelCoefficient,exponent,Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  change read n D G modulus c = residueBits (((levelCoefficient (n c) (D c) (G c) : ℤ) : ZMod m))
  rw [HE]
  simp only [read,BinaryNat.powMod_eq_bits,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,
    Nat.fromBitsLE_bits,residueBits,ZMod.val_natCast,m]

end LeanCanny.Encoding.LevelLiftCoefficient
