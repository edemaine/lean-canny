/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # Exact native univariate encoding of a streamed integer MV polynomial -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthKroneckerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

noncomputable def value (A W : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool→List Bool) (c : List Bool) : List Bool :=
  residueBits ((((FixedWidthKronecker.encode (A c) (W c) (p c)).coeff (Nat.fromBitsLE (target c))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c)+1))

theorem evaluator (A W D : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool→List Bool) (hA : UnaryFn A) (hW : UnaryFn W) (ht : target∈FP)
    (hD : ∀ c,(p c).totalDegree≤D c) (hfit : ∀ c,D c<2^W c)
    (E : SpaceFunction (FixedWidthRowBits.value A W p target modulus)) : SpaceFunction (value A W p target modulus) :=by
  have HB : BinaryFn (fun c=>count (A c) (W c)):=
    BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP hA hW) (fun c=>countCode_code A W c))
  have HG := (BinaryFn.fromBits ht).lt HB
  have H:=SpaceFunction.branch (fun c=>decide (Nat.fromBitsLE (target c)<count (A c) (W c)))
    HG.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun c=>?_)
  unfold value FixedWidthRowBits.value
  by_cases hu : Nat.fromBitsLE (target c)<count (A c) (W c)
  · simp only [hu,decide_true,ite_true]
    have HC:=FixedWidthKronecker.native_coefficient (Equiv.refl _) (W c) (D c) (p c)
      (hD c) (hfit c) (Nat.fromBitsLE (target c)) hu
    have HE : (FixedWidthKronecker.encode (A c) (W c) (p c)).coeff (Nat.fromBitsLE (target c))=
        (p c).coeff (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c))) :=by
      simpa [FixedWidthKronecker.native] using HC
    rw [HE]
  · simp only [hu,decide_false,Bool.false_eq_true,ite_false]
    have HF (e) (he : e∈(p c).support) (i) : e i<2^W c :=
      ((MvPolynomial.monomial_le_degreeOf i he).trans
        ((MvPolynomial.degreeOf_le_totalDegree _ i).trans (hD c))).trans_lt (hfit c)
    rw [FixedWidthKronecker.coefficient_of_ge _ _ _ HF _ (by omega)]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

end LeanCanny.Algebra.FixedWidthKroneckerBits
