/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialParameterShift
public import LeanCanny.Algebra.RationalMonomialWindowSpace
/-! # Native numerator coefficients for same-tuple parameter shifts -/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialParameterShift
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalMonomialWindowQuery
open scoped Classical

noncomputable def numeratorAt (F : Family) (negative : Bool) (c : List Bool) (i : ℕ) :
    MvPolynomial (Fin (F.arity c+1)) ℤ :=
  if i=0 then parameterNumerator F negative c
    else FixedWidthMonomialBits.polynomial (fun c=>F.arity c+1) (fun _=>i) (fun _=>1) F.scalars.denominator c

theorem numeratorAt_eq (F : Family) (negative : Bool) (c : List Bool) (i : Fin (F.arity c+1)) :
    numeratorAt F negative c i.val=numerator F negative c i :=by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [numeratorAt,Fin.val_zero,ite_true,numerator,Fin.cases_zero]
  · simp only [numeratorAt,Fin.val_succ,Nat.add_one_ne_zero,ite_false,numerator,Fin.cases_succ,
      FixedWidthMonomialBits.polynomial]
    rw [dite_eq_left (Nat.add_lt_add_right j.isLt 1),MvPolynomial.C_mul_X_eq_monomial]
    rfl

theorem numeratorAt_degree (F : Family) (negative : Bool) (c : List Bool) (i : ℕ) :
    (numeratorAt F negative c i).totalDegree≤F.weight c+1 :=by
  unfold numeratorAt
  split_ifs with h0
  · exact numerator_degree F negative c 0
  · unfold FixedWidthMonomialBits.polynomial
    split_ifs
    · exact (MvPolynomial.totalDegree_monomial_le _ _).trans
        (by simp)
    · simp

theorem coefficient_evaluator (F : Family) (negative : Bool) (W i : List Bool→ℕ)
    (target modulus : List Bool→List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hidx : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hi : BinaryFn i) (ht : target∈FP) (hm : modulus∈FP)
    (ED : SpaceFunction (fun c=>residueBits (F.scalars.denominator c : ZMod (Nat.fromBitsLE (modulus c)+1))))
    (EN : SpaceFunction (fun c=>residueBits (F.scalars.numerator c : ZMod (Nat.fromBitsLE (modulus c)+1)))) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>numeratorAt F negative c (i c)) target modulus) :=by
  have HA:=hA.add (UnaryFn.const 1)
  have ER:=FixedWidthMonomialBits.coefficient_evaluator F.arity W F.index F.weight
    (IntegerParameterCoefficientBits.spatial W target) F.scalars.numerator modulus _ EN (fun _=>rfl)
    hA hW hidx hw (IntegerParameterCoefficientBits.spatial_mem_FP W target hW ht)
  have ET : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>MvPolynomial.rename Fin.succ (base F c)) target modulus) :=
    FixedWidthHeadLiftBits.evaluator F.arity W (base F) target modulus hW ht ER
  have ED0:=FixedWidthMonomialBits.coefficient_evaluator (fun c=>F.arity c+1) W (fun _=>0) (fun _=>1)
    target F.scalars.denominator modulus _ ED (fun _=>rfl) HA hW (BinaryFn.const 0) (BinaryFn.const 1) ht
  have EX : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W
      (fun c=>MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0) target modulus) :=by
    refine ED0.congr (funext fun c=>?_)
    unfold FixedWidthRowBits.value
    congr 3
    simp only [FixedWidthMonomialBits.polynomial,Nat.zero_lt_succ,dite_true,MvPolynomial.C_mul_X_eq_monomial]
    rfl
  have EP : SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) W (parameterNumerator F negative) target modulus) :=
    FixedWidthRowBits.combine_evaluator negative _ W _ _ target modulus hm ET EX
  have EI:=FixedWidthMonomialBits.coefficient_evaluator (fun c=>F.arity c+1) W i (fun _=>1)
    target F.scalars.denominator modulus _ ED (fun _=>rfl) HA hW hi (BinaryFn.const 1) ht
  have EB:=FixedWidthRowBits.branch_evaluator _ W (parameterNumerator F negative)
    (fun c=>FixedWidthMonomialBits.polynomial (fun c=>F.arity c+1) i (fun _=>1) F.scalars.denominator c)
    target modulus (fun c=>i c=0) (hi.eq (BinaryFn.const 0)) EP EI
  have HP : (fun c=>if i c=0 then parameterNumerator F negative c else
      FixedWidthMonomialBits.polynomial (fun c=>F.arity c+1) i (fun _=>1) F.scalars.denominator c)=
      (fun c=>numeratorAt F negative c (i c)) :=by
    funext c
    unfold numeratorAt
    split_ifs <;> rfl
  exact EB.congr (congrArg (fun p=>FixedWidthRowBits.value (fun c=>F.arity c+1) W p target modulus) HP)

end LeanCanny.Algebra.RationalMonomialParameterShift
