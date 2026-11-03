/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateReader
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # Original bivariate coefficient readers supply arbitrary integer-MV rows

Repacking always bounds the queried index, including malformed input words.
Source context, chosen outer coefficient and caller modulus remain explicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

theorem coefficient_repack (A W : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (target : List Bool→List Bool) (c : List Bool) (hfit : (p c).totalDegree<2^W c) :
    (FixedWidthKronecker.encode (A c) (W c) (p c)).coeff
      (Nat.fromBitsLE (FixedWidthQuery.repack A W A W target c))=
        (p c).coeff (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c))) :=by
  have HU : Nat.fromBitsLE (FixedWidthQuery.repack A W A W target c)<count (A c) (W c) :=by
    have H:=Nat.fromBitsLE_lt_pow_length (FixedWidthQuery.repack A W A W target c)
    rw [FixedWidthQuery.repack_length] at H
    simpa only [count,←pow_mul,Nat.mul_comm (W c)] using H
  have HC:=FixedWidthKronecker.native_coefficient (Equiv.refl _) (W c) (p c).totalDegree (p c) le_rfl hfit _ HU
  have HE : (FixedWidthKronecker.encode (A c) (W c) (p c)).coeff
      (Nat.fromBitsLE (FixedWidthQuery.repack A W A W target c))=
        (p c).coeff (nativeExponent (Equiv.refl _) (W c)
          (Nat.fromBitsLE (FixedWidthQuery.repack A W A W target c))) :=by
    simpa [FixedWidthKronecker.native] using HC
  exact HE.trans (congrArg (p c).coeff (nativeExponent_repack (Equiv.refl _) W W target c le_rfl))

def rankCode (A W : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :=
  BinaryNat.normalize (FixedWidthQuery.repack A W A W target c)

def query (A W : List Bool→ℕ) (read : List Bool→List Bool) (y : List Bool→ℕ)
    (target modulus : List Bool→List Bool) (c : List Bool) :=
  pair (pair (read c) (modulus c))
    (pair (rankCode (A ∘ read) (W ∘ read) target c) (BinaryNatCode.encode (y c)))

theorem query_FP (A W : List Bool→ℕ) (read : List Bool→List Bool) (y : List Bool→ℕ)
    (target modulus : List Bool→List Bool) (hA : UnaryFn A) (hW : UnaryFn W) (hr : read∈FP)
    (hy : BinaryFn y) (ht : target∈FP) (hm : modulus∈FP) : query A W read y target modulus∈FP :=by
  have HA:=hA.comp hr
  have HW:=hW.comp hr
  have HU:=mem_FP_comp (FixedWidthQuery.repack_mem_FP HA HW HA HW ht) BinaryNat.normalize_mem_FP
  exact mem_FP_pair (mem_FP_pair hr hm) (mem_FP_pair HU hy.bits_mem_FP)

theorem evaluator (A W : List Bool→ℕ) (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀ c y,((p c).coeff y).totalDegree<2^W c)
    (read : List Bool→List Bool) (hr : read∈FP) (y : List Bool→ℕ) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (A ∘ read) (W ∘ read)
      (fun c=>(p (read c)).coeff (y c)) target modulus) :=by
  have E:=R.evaluator.precompose (query A W read y target modulus) (query_FP A W read y target modulus hA hW hr hy ht hm)
  refine E.congr (funext fun c=>?_)
  change R.coefficient (query A W read y target modulus c)=_
  unfold query rankCode
  rw [BinaryNat.normalize_eq_bits]
  refine (R.coefficient_eq (pair (read c) (modulus c))
    (Nat.fromBitsLE (FixedWidthQuery.repack (A ∘ read) (W ∘ read) (A ∘ read) (W ∘ read) target c)) (y c)).trans ?_
  unfold FixedWidthRowBits.value
  apply congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
  · rw [pairFst_pair,FixedWidthBivariateReader.polynomial,Polynomial.coeff_map]
    exact coefficient_repack (A ∘ read) (W ∘ read) (fun c=>(p (read c)).coeff (y c)) target c (hfit _ _)
  · rw [pairSnd_pair]

end LeanCanny.Algebra.FixedWidthBivariateRowBits
