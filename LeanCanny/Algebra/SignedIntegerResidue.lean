/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignStatisticSpace
public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native residues from signed integer output words -/

@[expose] public section
namespace LeanCanny.Algebra.SignedIntegerResidue
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairFst q)
def positive (q : List Bool) : List Bool := BinaryNat.mod (pair (pairFst (pairSnd q)) (modulus q))
def negative (q : List Bool) : List Bool := BinaryNat.mod (pair (pairSnd (pairSnd q)) (modulus q))
def value (q : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (modulus q)
    (pair (positive q) (ArithmeticBits.negate (pair (modulus q) (negative q)))))

theorem value_FP : value ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP BinaryNat.succ_mem_FP
  have hp := mem_FP_comp (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hm) BinaryNat.mod_mem_FP
  have hn := mem_FP_comp (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) hm) BinaryNat.mod_mem_FP
  have hneg := mem_FP_comp (mem_FP_pair hm hn) ArithmeticBits.negate_mem_FP
  have H := mem_FP_comp (mem_FP_pair hm (mem_FP_pair hp hneg)) ArithmeticBits.addMod_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [value, modulus, positive, negative, Function.comp_apply])

theorem packet (m : List Bool) (z : ℤ) : value (pair m (SignStatisticBits.integerCode z)) =
    residueBits (z : ZMod (Nat.fromBitsLE m + 1)) := by
  let n := Nat.fromBitsLE m + 1
  let : NeZero n := ⟨by dsimp [n]; omega⟩
  have hres (k : ℕ) : BinaryNat.mod (pair (BinaryNatCode.encode k) (BinaryNatCode.encode n)) =
      residueBits (k : ZMod n) := by
    simp only [BinaryNat.mod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast]
  simp only [value, positive, negative, modulus, pairFst_pair, pairSnd_pair, SignStatisticBits.integerCode,
    BinaryNat.succ_eq_bits]
  change ArithmeticBits.addMod (pair (BinaryNatCode.encode n)
    (pair (BinaryNat.mod (pair (BinaryNatCode.encode z.toNat) (BinaryNatCode.encode n)))
      (ArithmeticBits.negate (pair (BinaryNatCode.encode n)
        (BinaryNat.mod (pair (BinaryNatCode.encode (-z).toNat) (BinaryNatCode.encode n))))))) = _
  rw [hres, hres, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  have he : (z.toNat : ℤ) - (-z).toNat = z := by omega
  apply congrArg residueBits
  simpa only [Int.coe_castRingHom, Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_natCast, sub_eq_add_neg] using
    congrArg (Int.castRingHom (ZMod n)) he

attribute [local irreducible] value

theorem evaluator {z : List Bool → ℤ} (E : SpaceFunction (fun c => SignStatisticBits.integerCode (z c)))
    {mod : List Bool → List Bool} (hm : mod ∈ FP) :
    SpaceFunction (fun c => residueBits (z c : ZMod (Nat.fromBitsLE (mod c) + 1))) := by
  have M := SpaceFunction.ofFP mod hm
  have H := (M.pairOutputs E).postcompose value value_FP
  have he : (fun c => value (pair (mod c) (SignStatisticBits.integerCode (z c)))) =
      (fun c => residueBits (z c : ZMod (Nat.fromBitsLE (mod c) + 1))) :=
    funext (fun c => packet (mod c) (z c))
  exact H.congr he

end LeanCanny.Algebra.SignedIntegerResidue
