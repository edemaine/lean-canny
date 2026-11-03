/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialMidpoint
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSpace
public import LeanCanny.Algebra.ModularResidueSpace
/-! # Native two-sparse midpoint coefficients

Both old cofactor readers remain charged. Doubling the common integer uses
addition, including for even and nonunit caller moduli.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialMidpoint
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

theorem degreeBound_binary (F : Family) (hl : BinaryFn F.leftWeight) (hr : BinaryFn F.rightWeight) :
    BinaryFn (degreeBound F) :=(BinaryFn.ite (hl.le hr) hr hl).of_eq (fun _=>by simp only [degreeBound,max_def])

theorem massBound_binary (F : Family) (hl : BinaryFn F.left.mass) (hr : BinaryFn F.right.mass) :
    BinaryFn (massBound F) :=by
  have HM : BinaryFn (fun c=>max (F.left.mass c) (F.right.mass c)):=
    (BinaryFn.ite (hl.le hr) hr hl).of_eq (fun _=>by simp only [max_def])
  exact HM.add (BinaryFn.const 1)

theorem coefficient_evaluator (F : Family) (W : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hl : BinaryFn F.leftIndex) (hr : BinaryFn F.rightIndex)
    (hwl : BinaryFn F.leftWeight) (hwr : BinaryFn F.rightWeight) (ht : target∈FP) (hm : modulus∈FP)
    (EL : SpaceFunction (fun c=>residueBits (F.left.numerator c : ZMod (Nat.fromBitsLE (modulus c)+1))))
    (ER : SpaceFunction (fun c=>residueBits (F.right.numerator c : ZMod (Nat.fromBitsLE (modulus c)+1)))) :
    SpaceFunction (FixedWidthRowBits.value F.arity W (numerator F) target modulus) :=
  FixedWidthRowBits.add_evaluator F.arity W (leftPolynomial F) (rightPolynomial F) target modulus hm
    (FixedWidthMonomialBits.coefficient_evaluator F.arity W F.leftIndex F.leftWeight target F.left.numerator
      modulus _ EL (fun _=>rfl) hA hW hl hwl ht)
    (FixedWidthMonomialBits.coefficient_evaluator F.arity W F.rightIndex F.rightWeight target F.right.numerator
      modulus _ ER (fun _=>rfl) hA hW hr hwr ht)

theorem denominator_evaluator (F : Family) (modulus : List Bool→List Bool) (hm : modulus∈FP)
    (ED : SpaceFunction (fun c=>residueBits (F.left.denominator c : ZMod (Nat.fromBitsLE (modulus c)+1)))) :
    SpaceFunction (fun c=>residueBits (denominator F c : ZMod (Nat.fromBitsLE (modulus c)+1))) :=by
  have E:=ModularResidueSpace.addEvaluator modulus _ _ hm ED ED
  refine E.congr (funext fun c=>?_)
  apply congrArg residueBits
  simp only [denominator,two_mul,Int.cast_add]

noncomputable def pull (F : Family) (f : List Bool→List Bool) : Family where
  arity c:=F.arity (f c)
  leftIndex c:=F.leftIndex (f c)
  rightIndex c:=F.rightIndex (f c)
  leftWeight c:=F.leftWeight (f c)
  rightWeight c:=F.rightWeight (f c)
  left:={
    numerator c:=F.left.numerator (f c)
    denominator c:=F.left.denominator (f c)
    mass c:=F.left.mass (f c)
    numerator_bound c:=F.left.numerator_bound (f c)
    denominator_bound c:=F.left.denominator_bound (f c) }
  right:={
    numerator c:=F.right.numerator (f c)
    denominator c:=F.right.denominator (f c)
    mass c:=F.right.mass (f c)
    numerator_bound c:=F.right.numerator_bound (f c)
    denominator_bound c:=F.right.denominator_bound (f c) }
  sameDenominator c:=F.sameDenominator (f c)

def scalarPacket (q : List Bool) :=pair (pair (RationalSubstitution.IntegerBits.context q) []) (pairSnd q)

theorem scalarPacket_FP : scalarPacket∈FP:=by polytime [scalarPacket,RationalSubstitution.IntegerBits.context]

theorem scalar_residue_evaluator (S : IntegerPolynomialRationalPointSource.Scalars)
    (A : IntegerPolynomialRationalPointSource.Access S) (num : Bool) :
    SpaceFunction (fun q=>residueBits
      ((if num then S.numerator (RationalSubstitution.IntegerBits.context q)
        else S.denominator (RationalSubstitution.IntegerBits.context q)) : ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=by
  cases num with
  | false =>
    refine (A.denominator.precompose scalarPacket scalarPacket_FP).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])
  | true =>
    refine (A.numerator.precompose scalarPacket scalarPacket_FP).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])

end LeanCanny.Algebra.RationalMonomialMidpoint
