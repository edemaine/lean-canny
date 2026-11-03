/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # Native exact-width parameter blocks before an existing raw exponent word -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthParameterConsBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open scoped Classical

def prepend (W k : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  FixedWidthNatVector.encode 1 (W c) (fun _=>k c)++target c

theorem prepend_FP (W k : List Bool→ℕ) (target : List Bool→List Bool)
    (hW : UnaryFn W) (hk : BinaryFn k) (ht : target∈FP) : prepend W k target∈FP :=by
  have HP:=FixedWidthNatVector.encode_mem_FP (fun _=>1) W (fun c _=>k c) (UnaryFn.const 1) hW
    (fun q=>BinaryNatCode.encode (k (pairFst q))) (mem_FP_comp pairFst_mem_FP hk.bits_mem_FP)
    (fun c i=>by simp only [pairFst_pair])
  exact appendFn_mem_FP HP ht

theorem nativeExponent_prepend (m w k : ℕ) (bits : List Bool) (hk : k<2^w) :
    nativeExponent (Equiv.refl (Fin (m+1))) w
      (Nat.fromBitsLE (FixedWidthNatVector.encode 1 w (fun _=>k)++bits))=
        (nativeExponent (Equiv.refl (Fin m)) w (Nat.fromBitsLE bits)).cons k :=by
  let blockWord:=FixedWidthNatVector.encode 1 w (fun _=>k)
  have HL : blockWord.length=w:=by simp [blockWord]
  have HD : (blockWord++bits).drop w=bits:=List.drop_left' HL
  have HT : (blockWord++bits).take w=blockWord:=List.take_left' HL
  have HV : Nat.fromBitsLE blockWord=k :=by
    have H:=FixedWidthNatVector.decode_block 1 w (fun _=>k) 0 (by decide) hk
    have HP : blockWord.take w=blockWord:=List.take_of_length_le HL.le
    simp only [Nat.zero_mul,List.drop_zero] at H
    change Nat.fromBitsLE (blockWord.take w)=k at H
    rw [HP] at H
    exact H
  have HP:=IntegerParameterCoefficientBits.parameter_nativeExponent (fun _=>w) (fun _=>blockWord++bits) m []
  have HS:=IntegerParameterCoefficientBits.tail_nativeExponent (fun _=>w) (fun _=>blockWord++bits) m []
  simp only [IntegerParameterCoefficientBits.parameter,BinaryNat.normalize_eq_bits,Nat.fromBitsLE_bits,HT] at HP
  simp only [IntegerParameterCoefficientBits.spatial,BinaryNat.normalize_eq_bits,Nat.fromBitsLE_bits,HD] at HS
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · rw [Finsupp.cons_zero]
    exact HP.trans HV
  · rw [Finsupp.cons_succ]
    exact congrArg (fun e : Fin m→₀ℕ=>e j) HS

def two (W δ ε : List Bool→ℕ) (target : List Bool→List Bool) :=prepend W δ (prepend W ε target)

theorem two_FP (W δ ε : List Bool→ℕ) (target : List Bool→List Bool)
    (hW : UnaryFn W) (hδ : BinaryFn δ) (hε : BinaryFn ε) (ht : target∈FP) : two W δ ε target∈FP :=
  prepend_FP W δ _ hW hδ (prepend_FP W ε target hW hε ht)

theorem nativeExponent_two (m w δ ε : ℕ) (bits : List Bool) (hδ : δ<2^w) (hε : ε<2^w) :
    nativeExponent (Equiv.refl (Fin (m+2))) w
      (Nat.fromBitsLE (FixedWidthNatVector.encode 1 w (fun _=>δ)++
        (FixedWidthNatVector.encode 1 w (fun _=>ε)++bits)))=
      ((nativeExponent (Equiv.refl (Fin m)) w (Nat.fromBitsLE bits)).cons ε).cons δ :=by
  rw [nativeExponent_prepend (m+1) w δ _ hδ,nativeExponent_prepend m w ε bits hε]

end LeanCanny.Algebra.FixedWidthParameterConsBits
