/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialWindowQuery
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSpace
public import LeanCanny.Algebra.FixedWidthHeadLiftSpace
/-! # Native sparse window coefficients from two charged integer scalars

The binary monomial power is never expanded. Modular products clear the
window with the square of the denominator, without modular division.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialWindowQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

private theorem zero_row (A W : List Bool→ℕ) (target modulus : List Bool→List Bool) :
    SpaceFunction (FixedWidthRowBits.value A W (fun _=>0) target modulus) :=by
  refine (SpaceFunction.ofFP (fun _ : List Bool=>[]) (constFn_mem_FP [])).congr (funext fun c=>?_)
  simp only [FixedWidthRowBits.value,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Int.cast_zero,
    residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem coefficient_evaluator (F : Family) (negative : Bool)
    (W y : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hy : BinaryFn y) (ht : target∈FP) (hm : modulus∈FP)
    (ED : SpaceFunction (fun c=>residueBits (F.scalars.denominator c : ZMod (Nat.fromBitsLE (modulus c)+1))))
    (EN : SpaceFunction (fun c=>residueBits (F.scalars.numerator c : ZMod (Nat.fromBitsLE (modulus c)+1)))) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>(query F negative c).coeff (y c)) target modulus) :=by
  have HA : UnaryFn (fun c=>F.arity c+1):=hA.add (UnaryFn.const 1)
  have EDD:=ModularResidueSpace.mulEvaluator modulus _ _ hm ED ED
  have ED2 : SpaceFunction (fun c=>residueBits ((F.scalars.denominator c^2 : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))) :=
    EDD.congr (funext fun c=>by simp only [pow_two,Int.cast_mul])
  have EDN:=ModularResidueSpace.mulEvaluator modulus _ _ hm ED EN
  have Eprod : SpaceFunction (fun c=>residueBits
      ((F.scalars.denominator c*F.scalars.numerator c : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))) :=
    EDN.congr (funext fun c=>by simp only [Int.cast_mul])
  have ER:=FixedWidthMonomialBits.coefficient_evaluator F.arity W F.index F.weight
    (IntegerParameterCoefficientBits.spatial W target)
    (fun c=>F.scalars.denominator c*F.scalars.numerator c) modulus _ Eprod (fun _=>rfl)
    hA hW hi hw (IntegerParameterCoefficientBits.spatial_mem_FP W target hW ht)
  have ET : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>MvPolynomial.rename Fin.succ (raw F c)) target modulus) :=
    FixedWidthHeadLiftBits.evaluator F.arity W (raw F) target modulus hW ht ER
  have EE:=FixedWidthMonomialBits.coefficient_evaluator (fun c=>F.arity c+1) W (fun _=>0) (fun _=>1)
    target (fun c=>F.scalars.denominator c^2) modulus _ ED2 (fun _=>rfl)
    HA hW (BinaryFn.const 0) (BinaryFn.const 1) ht
  have EE' : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W (epsilon F) target modulus) :=by
    refine EE.congr (funext fun c=>?_)
    unfold FixedWidthRowBits.value
    congr 3
    simp only [FixedWidthMonomialBits.polynomial,Nat.zero_lt_succ,dite_true,epsilon,
      MvPolynomial.C_mul_X_eq_monomial]
    rfl
  have Eeps : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>if negative then -epsilon F c else epsilon F c) target modulus) :=by
    cases negative
    · exact EE'
    · simpa only [ite_true,zero_sub] using FixedWidthRowBits.sub_evaluator _ W
        (fun _=>0) (epsilon F) target modulus hm (zero_row _ W target modulus) EE'
  have EB : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W (body F negative) target modulus) :=
    FixedWidthRowBits.sub_evaluator _ W _ _ target modulus hm Eeps ET
  have EC : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>MvPolynomial.C (F.scalars.denominator c^2)) target modulus) :=
    FixedWidthConstantBits.evaluator HA hW ht ED2 _ (fun _=>rfl)
  have E0:=FixedWidthRowBits.branch_evaluator _ W (body F negative) (fun _=>0) target modulus
    (fun c=>y c=0) (hy.eq (BinaryFn.const 0)) EB (zero_row _ W target modulus)
  have E1:=FixedWidthRowBits.branch_evaluator _ W (fun c=>MvPolynomial.C (F.scalars.denominator c^2))
    (fun c=>if y c=0 then body F negative c else 0) target modulus (fun c=>y c=1)
    (hy.eq (BinaryFn.const 1)) EC E0
  refine E1.congr (funext fun c=>?_)
  simp only [FixedWidthRowBits.value,coefficient]

end LeanCanny.Algebra.RationalMonomialWindowQuery
