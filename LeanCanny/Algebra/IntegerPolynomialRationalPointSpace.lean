/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSource
public import LeanCanny.Algebra.IntegerPolynomialExpandSpace
public import LeanCanny.Algebra.UnivariateRationalSpace
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Charged native readers for rational-monomial polynomial tests

The outer integer coefficient program and both scalar residue programs are
charged. Binary metadata suffices for the power, degree and mass bounds.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialRationalPointSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical

structure Access (A : Scalars) where
  mass : BinaryFn A.mass
  numerator : SpaceFunction (fun q=>residueBits (A.numerator (context q) : ZMod (mValue q)))
  denominator : SpaceFunction (fun q=>residueBits (A.denominator (context q) : ZMod (mValue q)))

private theorem zero_evaluator : SpaceFunction (fun q=>residueBits (0 : ZMod (mValue q))) :=
  (SpaceFunction.ofFP (fun _ : List Bool=>[]) (constFn_mem_FP [])).congr
    (funext fun _=>by simp [residueBits,BinaryNatCode.encode])

theorem linear_evaluator (A : Scalars) (hA : Access A) :
    SpaceFunction (PrimitivePairBits.coefficient (linear A)) := by
  have HK:=BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have E:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun q=>Nat.fromBitsLE (selectedDegree q)=1) (HK.eq (BinaryFn.const 1)) hA.numerator zero_evaluator
  refine E.congr (funext fun q=>?_)
  unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
  by_cases H : Nat.fromBitsLE (selectedDegree q)=1
  · simp only [H,ite_true,linear,Polynomial.coeff_C_mul,Polynomial.coeff_X_one,mul_one]
  · simp only [H,ite_false,linear,Polynomial.coeff_C_mul,Polynomial.coeff_X_of_ne_one H,mul_zero,Int.cast_zero]

theorem constant_evaluator (A : Scalars) (hA : Access A) :
    SpaceFunction (PrimitivePairBits.coefficient (constant A)) := by
  have HK:=BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have E:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun q=>Nat.fromBitsLE (selectedDegree q)=0) (HK.eq (BinaryFn.const 0)) hA.denominator zero_evaluator
  refine E.congr (funext fun q=>?_)
  unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
  by_cases H : Nat.fromBitsLE (selectedDegree q)=0 <;>
    simp only [constant,Polynomial.coeff_C,H,ite_true,ite_false,Int.cast_zero]

theorem cleared_access (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (A : Scalars) (hA : Access A) : IntegerPolynomialRootQueriesBits.Access (clearedSource S A) where
  coefficient:=UnivariateRationalBits.evaluator S.polynomial (linear A) (constant A) _
    ((BinaryFn.const 2).mul hS.degree) hS.coefficient (linear_evaluator A hA) (constant_evaluator A hA)
  degree:=(BinaryFn.const 2).mul hS.degree
  mass:=hS.mass.add (((BinaryFn.const 2).mul hS.degree).mul hA.mass)

theorem access (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (A : Scalars) (hA : Access A) {w : List Bool→ℕ} (hw : BinaryFn w) (hpos : ∀ c,0<w c) :
    IntegerPolynomialRootQueriesBits.Access (source S A w) :=
  IntegerPolynomialExpandSource.access (clearedSource S A) (cleared_access S hS A hA) hw hpos

end LeanCanny.Algebra.IntegerPolynomialRationalPointSource
