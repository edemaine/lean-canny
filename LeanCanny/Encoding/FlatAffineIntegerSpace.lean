/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourceTower
public import LeanCanny.Algebra.ModularAddFP

/-! # Native signed integer entries of affine tower records

Signed fixed-width entries are reduced modulo the positive decoded modulus.
The record reader is charged even when it computes in polynomial space.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineIntegerSpace
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (W selected : List Bool → ℕ) (record modulus : List Bool → List Bool)

def positive (c : List Bool) : List Bool :=
  BinaryNat.normalize (((record c).drop (selected c * (2 * W c))).take (W c))
def negative (c : List Bool) : List Bool :=
  BinaryNat.normalize (((record c).drop (selected c * (2 * W c) + W c)).take (W c))
def modulusCode (c : List Bool) : List Bool := BinaryNat.add (pair (modulus c) [true])

theorem positive_FP (hW : UnaryFn W) (hs : UnaryFn selected) (hr : record ∈ FP) : positive W selected record ∈ FP :=
  mem_FP_comp (take_mem_FP (drop_mem_FP hr (hs.mul ((UnaryFn.const 2).mul hW))) hW) BinaryNat.normalize_mem_FP

theorem negative_FP (hW : UnaryFn W) (hs : UnaryFn selected) (hr : record ∈ FP) : negative W selected record ∈ FP :=
  mem_FP_comp (take_mem_FP (drop_mem_FP hr ((hs.mul ((UnaryFn.const 2).mul hW)).add hW)) hW) BinaryNat.normalize_mem_FP

theorem modulusCode_FP (hm : modulus ∈ FP) : modulusCode modulus ∈ FP :=
  mem_FP_comp (mem_FP_pair hm (constFn_mem_FP [true])) BinaryNat.add_mem_FP

theorem modulusCode_eq (c : List Bool) :
    modulusCode modulus c = BinaryNatCode.encode (Nat.fromBitsLE (modulus c) + 1) := by
  rw [modulusCode, BinaryNat.add_pair]
  rfl

def positiveMod (c : List Bool) : List Bool := BinaryNat.mod (pair (positive W selected record c) (modulusCode modulus c))
def negativeMod (c : List Bool) : List Bool := BinaryNat.mod (pair (negative W selected record c) (modulusCode modulus c))
def code (c : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (modulusCode modulus c) (pair (positiveMod W selected record modulus c)
    (ArithmeticBits.negate (pair (modulusCode modulus c) (negativeMod W selected record modulus c)))))

noncomputable def value (c : List Bool) : List Bool := residueBits
  ((FlatAffineFullSourceTower.integer (W c) (record c) (selected c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate BinaryNat.mod

theorem code_FP (hW : UnaryFn W) (hs : UnaryFn selected) (hr : record ∈ FP) (hm : modulus ∈ FP) :
    code W selected record modulus ∈ FP := by
  have hM := modulusCode_FP modulus hm
  have hp := mem_FP_comp (mem_FP_pair (positive_FP W selected record hW hs hr) hM) BinaryNat.mod_mem_FP
  have hn := mem_FP_comp (mem_FP_pair (negative_FP W selected record hW hs hr) hM) BinaryNat.mod_mem_FP
  change positiveMod W selected record modulus ∈ FP at hp
  change negativeMod W selected record modulus ∈ FP at hn
  have hneg := mem_FP_comp (mem_FP_pair hM hn) ArithmeticBits.negate_mem_FP
  exact mem_FP_comp (mem_FP_pair hM (mem_FP_pair hp hneg)) ArithmeticBits.addMod_mem_FP

theorem code_eq (c : List Bool) : code W selected record modulus c = value W selected record modulus c := by
  let m := Nat.fromBitsLE (modulus c) + 1
  have hp : positiveMod W selected record modulus c =
      residueBits ((Nat.fromBitsLE (((record c).drop (selected c * (2 * W c))).take (W c)) : ℕ) : ZMod m) := by
    simp only [positiveMod, positive, modulusCode_eq, BinaryNat.mod_pair, BinaryNat.normalize_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast, m]
  have hn : negativeMod W selected record modulus c =
      residueBits ((Nat.fromBitsLE (((record c).drop (selected c * (2 * W c) + W c)).take (W c)) : ℕ) : ZMod m) := by
    simp only [negativeMod, negative, modulusCode_eq, BinaryNat.mod_pair, BinaryNat.normalize_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast, m]
  rw [code, hp, hn, modulusCode_eq, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  unfold value
  apply congrArg residueBits
  simp only [FlatAffineFullSourceTower.integer, Int.cast_sub, Int.cast_natCast]
  exact sub_eq_add_neg _ _ |>.symm

theorem value_FP (hW : UnaryFn W) (hs : UnaryFn selected) (hr : record ∈ FP) (hm : modulus ∈ FP) :
    value W selected record modulus ∈ FP :=
  mem_FP_of_eq (code_FP W selected record modulus hW hs hr hm) (code_eq W selected record modulus)

theorem evaluator (hW : UnaryFn W) (hs : UnaryFn selected) (hr : SpaceFunction record) (hm : modulus ∈ FP) :
    SpaceFunction (value W selected record modulus) := by
  have hc := value_FP (W ∘ pairFst) (selected ∘ pairFst) pairSnd (modulus ∘ pairFst)
    (hW.comp pairFst_mem_FP) (hs.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  have he (z : List Bool) : value (W ∘ pairFst) (selected ∘ pairFst) pairSnd (modulus ∘ pairFst) z =
      value W selected (fun _ => pairSnd z) modulus (pairFst z) := rfl
  exact (hr.withInput.postcompose _ hc).congr (funext fun c => by
    change value (W ∘ pairFst) (selected ∘ pairFst) pairSnd (modulus ∘ pairFst) (pair c (record c)) = _
    rw [he, pairFst_pair, pairSnd_pair]
    rfl)

end LeanCanny.Encoding.FlatAffineIntegerSpace
