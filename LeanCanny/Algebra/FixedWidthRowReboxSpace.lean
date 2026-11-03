/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateRowSpace
public import LeanCanny.Encoding.FixedWidthQueryBinary
/-! # Changing a streamed coefficient box without wrapping exponents

A native guard checks every requested exponent against the old box before
repacking. The caller modulus and the original coefficient cost are retained.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthRowReboxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A U V : List Bool→ℕ) (target : List Bool→List Bool)

def Fits :=FixedWidthQuery.Bounded A V target (fun c=>2^U c-1)

theorem fits_FP (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V) (ht : target∈FP) :
    FPPred (Fits A U V target) :=
  FixedWidthQuery.bounded_binary_fppred hA hV (((BinaryFn.const 2).powUnary hU).sub (BinaryFn.const 1)) ht

theorem exponent_repack (c : List Bool) (h : Fits A U V target c) :
    nativeExponent (Equiv.refl (Fin (A c))) (U c)
      (Nat.fromBitsLE (FixedWidthQuery.repack A V A U target c))=
        nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c)) :=by
  ext i
  simp only [nativeExponent,Finsupp.coe_equivFunOnFinite_symm,Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits]
  have HB : FixedWidthQuery.entry A V target c i.val<2^U c :=by
    rw [FixedWidthQuery.entry,ite_eq_left i.isLt]
    have H:=h i.val i.isLt
    change FixedWidthQuery.coordinate V target c i.val≤2^U c-1 at H
    have HP:=Nat.two_pow_pos (U c)
    omega
  simpa only [FixedWidthQuery.entry,ite_eq_left i.isLt,FixedWidthQuery.coordinate] using
    FixedWidthQuery.coordinate_repack A V A U target c i.val i.isLt HB

theorem coefficient_zero (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (c : List Bool) (hp : (p c).totalDegree<2^U c) (h : ¬Fits A U V target c) :
    (p c).coeff (nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c)))=0 :=by
  by_contra H
  have HS:=MvPolynomial.mem_support_iff.mpr H
  apply h
  intro i hi
  have HL:=(MvPolynomial.monomial_le_degreeOf (⟨i,hi⟩ : Fin (A c)) HS).trans
    (MvPolynomial.degreeOf_le_totalDegree _ _)
  have HE : nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c)) ⟨i,hi⟩=
      FixedWidthQuery.coordinate V target c i :=by
    simp only [nativeExponent,Finsupp.coe_equivFunOnFinite_symm,Equiv.refl_apply,
      FixedWidthBlockRenameBits.entry_bits,FixedWidthQuery.coordinate]
  rw [HE] at HL
  change FixedWidthQuery.coordinate V target c i≤2^U c-1
  have HP:=Nat.two_pow_pos (U c)
  omega

theorem evaluator (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ) (modulus : List Bool→List Bool)
    (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V) (ht : target∈FP)
    (hp : ∀ c,(p c).totalDegree<2^U c)
    (E : SpaceFunction (FixedWidthRowBits.value A U p (FixedWidthQuery.repack A V A U target) modulus)) :
    SpaceFunction (FixedWidthRowBits.value A V p target modulus) :=by
  have EB:=SpaceFunction.branch (fun c=>decide (Fits A U V target c))
    (fits_FP A U V target hA hU hV ht).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c=>?_)
  by_cases HC : Fits A U V target c
  · simp only [HC,decide_true,ite_true,FixedWidthRowBits.value]
    rw [exponent_repack A U V target c HC]
  · simp only [HC,decide_false,Bool.false_eq_true,ite_false,FixedWidthRowBits.value,
      coefficient_zero A U V target p c (hp c) HC,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

end LeanCanny.Algebra.FixedWidthRowReboxBits
