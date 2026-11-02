/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineVectorFP
public import LeanCanny.Algebra.SignedIntegerArithmeticFP
public import LeanCanny.ETR.NumericLiteralFP
/-! # Native literal affine entries from the original fixed-width level words -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedAffineCode
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def positive (w : List Bool) := Nat.fromBitsLE (pairFst (SignedIntegerArithmetic.canonical w))
def negative (w : List Bool) := Nat.fromBitsLE (pairSnd (SignedIntegerArithmetic.canonical w))
def integerLiteral (w : List Bool) :=
  if negative w = 0 then (ETR.Term.const (positive w : ℤ)).toData.toBits
  else (ETR.Term.const (-(negative w : ℤ))).toData.toBits

attribute [local irreducible] SignedIntegerArithmetic.canonical

theorem integerLiteral_FP : integerLiteral ∈ FP := by
  have HP : BinaryFn positive := BinaryFn.fromBits (f := fun w => pairFst (SignedIntegerArithmetic.canonical w)) (mem_FP_comp (f := SignedIntegerArithmetic.canonical) (g := pairFst) SignedIntegerArithmetic.canonical_FP pairFst_mem_FP)
  have HN : BinaryFn negative := BinaryFn.fromBits (f := fun w => pairSnd (SignedIntegerArithmetic.canonical w)) (mem_FP_comp (f := SignedIntegerArithmetic.canonical) (g := pairSnd) SignedIntegerArithmetic.canonical_FP pairSnd_mem_FP)
  exact (HN.eq (BinaryFn.const 0)).ite_mem_FP (ETR.Term.nat_toBits_mem_FP HP) (ETR.Term.negNat_toBits_mem_FP HN)

theorem integerLiteral_eq (w : List Bool) :
    integerLiteral w = (ETR.Term.const (SignedIntegerArithmetic.value w)).toData.toBits := by
  have HP : positive w = (SignedIntegerArithmetic.value w).toNat := by
    simp only [positive, SignedIntegerArithmetic.canonical_eq, SignStatisticBits.integerCode, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HN : negative w = (-SignedIntegerArithmetic.value w).toNat := by
    simp only [negative, SignedIntegerArithmetic.canonical_eq, SignStatisticBits.integerCode, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold integerLiteral
  rw [HP, HN]
  split_ifs with hn
  · apply congrArg (fun z : ℤ => (ETR.Term.const z).toData.toBits)
    omega
  · apply congrArg (fun z : ℤ => (ETR.Term.const z).toData.toBits)
    omega

def signedSlice (W I : List Bool → ℕ) (V : List Bool → List Bool) (q : List Bool) :=
  pair (((V q).drop (I q * (2 * W q))).take (W q))
    (((V q).drop (I q * (2 * W q) + W q)).take (W q))

theorem signedSlice_FP (W I : List Bool → ℕ) (V : List Bool → List Bool)
    (hW : UnaryFn W) (hI : UnaryFn I) (hV : V ∈ FP) : signedSlice W I V ∈ FP := by
  have HN := hI.mul ((UnaryFn.const 2).mul hW)
  exact mem_FP_pair (take_mem_FP (drop_mem_FP hV HN) hW) (take_mem_FP (drop_mem_FP hV (HN.add hW)) hW)

theorem signedSlice_value (W I : List Bool → ℕ) (V : List Bool → List Bool) (q : List Bool) :
    SignedIntegerArithmetic.value (signedSlice W I V q) = FlatAffineFullSourceTower.integer (W q) (V q) (I q) := by
  simp only [SignedIntegerArithmetic.value, signedSlice, pairFst_pair, pairSnd_pair, FlatAffineFullSourceTower.integer]

theorem scaledReference_FP (W I R : List Bool → ℕ) (V : List Bool → List Bool)
    (hW : UnaryFn W) (hI : UnaryFn I) (hR : UnaryFn R) (hV : V ∈ FP) :
    (fun q => encode (.scale (FlatAffineFullSourceTower.integer (W q) (V q) (I q)) (.reference (R q)))) ∈ FP := by
  have HL := mem_FP_comp (f := signedSlice W I V) (g := integerLiteral) (signedSlice_FP W I V hW hI hV) integerLiteral_FP
  have HR := ETR.Term.variableBits_mem_FP hR
  have H := ETR.Codec.taggedTwo_mem_FP 3 HL HR
  exact mem_FP_of_eq H (fun q => by
    simp only [Function.comp_apply, integerLiteral_eq, signedSlice_value, ETR.Term.variableBits_eq, encode, term, ETR.Term.mul_toBits])
end LeanCanny.Algebra.IntegralMixedAffineCode
