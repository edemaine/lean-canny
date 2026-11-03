/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialBivariateShift
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # An original bivariate reader supplies the entire shifted coordinate head

The same endpoint, old raw tuple and clearing allowance serve every outer
coefficient. Both the original head cost and old-bank scalar costs are charged.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialBivariateShift
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open RationalMonomialWindowQuery
open RationalSubstitution.IntegerBits (context selectedDegree context_mem_FP selectedDegree_mem_FP)
open FixedWidthBivariateReboxBits (target modulus outer)
open scoped Classical

private def scalarQuery (f : List Bool→List Bool) (q : List Bool) :=pair (pair (f (context q)) []) (pairSnd q)

private theorem scalarQuery_FP (f : List Bool→List Bool) (hf : f∈FP) : scalarQuery f∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp context_mem_FP hf) (constFn_mem_FP [])) pairSnd_mem_FP

theorem pullAccess (F : Family) (A : IntegerPolynomialRationalPointSource.Access F.scalars)
    (f : List Bool→List Bool) (hf : f∈FP) : IntegerPolynomialRationalPointSource.Access (pull F f).scalars where
  mass:=A.mass.comp hf
  numerator:=by
    refine (A.numerator.precompose (scalarQuery f) (scalarQuery_FP f hf)).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarQuery,context,pairFst_pair];rfl)
      (by simp only [scalarQuery,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])
  denominator:=by
    refine (A.denominator.precompose (scalarQuery f) (scalarQuery_FP f hf)).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarQuery,context,pairFst_pair];rfl)
      (by simp only [scalarQuery,RationalSubstitution.IntegerBits.mValue,pairSnd_pair])

noncomputable def sourceValue (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) :=
  FixedWidthRowBits.value (fun q=>F.arity (FixedWidthBivariateReader.origin (context q))+1)
    (fun q=>W (FixedWidthBivariateReader.origin (context q)))
    (fun q=>(p (FixedWidthBivariateReader.origin (context q))).coeff (outer (context q))) selectedDegree pairSnd

private noncomputable def sourceEntry (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) (r : ℕ) (mw : List Bool) :=
  residueBits (((((p (FixedWidthBivariateReader.origin c)).coeff (outer c)).coeff
    (nativeExponent (Equiv.refl _) (W (FixedWidthBivariateReader.origin c)) r)) : ℤ) : ZMod (Nat.fromBitsLE mw+1))

private theorem source_entry (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (q : List Bool) :
    sourceValue F W p q=sourceEntry F W p (context q) (Nat.fromBitsLE (selectedDegree q)) (pairSnd q) :=rfl

private theorem sourceEntry_value (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) (r : ℕ) (mw : List Bool) :
    sourceEntry F W p c r mw=residueBits (((((p (FixedWidthBivariateReader.origin c)).coeff (outer c)).coeff
      (nativeExponent (Equiv.refl _) (W (FixedWidthBivariateReader.origin c)) r)) : ℤ) : ZMod (Nat.fromBitsLE mw+1)) :=rfl

attribute [local irreducible] sourceEntry

theorem source_packet (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) (r m : ℕ) (hm : 0<m) :
    sourceValue F W p (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m-1)))=
      residueBits (((((p (FixedWidthBivariateReader.origin c)).coeff (outer c)).coeff
        (nativeExponent (Equiv.refl _) (W (FixedWidthBivariateReader.origin c)) r)) : ℤ) : ZMod m) :=by
  rw [source_entry]
  have HE:=sourceEntry_value F W p c r (BinaryNatCode.encode (m-1))
  have HM : Nat.fromBitsLE (BinaryNatCode.encode (m-1))+1=m:=by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits];omega
  rw [HM] at HE
  rw [←HE]
  simp only [context,selectedDegree,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def coefficientWord (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) :=
  FixedWidthRowBits.value (fun z=>F.arity (FixedWidthBivariateReader.origin z)+1)
    (RationalMonomialParameterShift.nativeTargetWidth F W ∘ FixedWidthBivariateReader.origin)
    (fun z=>(head F negative W p (FixedWidthBivariateReader.origin z)).coeff (outer z)) target modulus

theorem coefficient_evaluator (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>F.arity c+1) W p))
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars)
    (hfit : ∀ c y,((p c).coeff y).totalDegree<2^W c) : SpaceFunction (coefficientWord F negative W p) :=by
  have HO:=FixedWidthBivariateReader.origin_FP
  have HY : BinaryFn outer:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HC:=mem_FP_comp context_mem_FP HO
  have ES:=FixedWidthBivariateRowBits.evaluator (fun c=>F.arity c+1) W p R
    (hA.add (UnaryFn.const 1)) hW hfit (FixedWidthBivariateReader.origin ∘ context) HC
    (outer ∘ context) (HY.comp context_mem_FP) selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  have HF (c : List Bool) (i) : ((p (FixedWidthBivariateReader.origin c)).coeff (outer c)).degreeOf i<
      2^(W ∘ FixedWidthBivariateReader.origin) c :=
    (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (hfit _ _)
  have E:=RationalMonomialParameterShift.evaluator (pull F FixedWidthBivariateReader.origin) negative
    (W ∘ FixedWidthBivariateReader.origin)
    (fun c=>(p (FixedWidthBivariateReader.origin c)).coeff (outer c)) HF
    (hA.comp HO) (hW.comp HO) (hi.comp HO) (hw.comp HO) (pullAccess F hS _ HO)
    (sourceValue F W p) ES (by
      intro c r _ m hm
      rw [source_packet F W p c r m hm]
      apply congrArg (fun a : ℤ=>residueBits (a : ZMod m))
      rw [nativeExponent_refl]
      rfl) target modulus (by polytime [target]) (by polytime [modulus])
  refine E.congr (funext fun z=>?_)
  unfold FixedWidthRowBits.value coefficientWord
  apply congrArg (fun a : ℤ=>residueBits (a : ZMod (Nat.fromBitsLE (modulus z)+1)))
  have HH:=coefficient_native F negative W p (fun c y i=>(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (hfit c y))
    (fun _=>outer z) (FixedWidthBivariateReader.origin z)
  exact congrArg (fun a : MvPolynomial (Fin (F.arity (FixedWidthBivariateReader.origin z)+1)) ℤ=>
    a.coeff (nativeExponent (Equiv.refl _) (RationalMonomialParameterShift.nativeTargetWidth F W
      (FixedWidthBivariateReader.origin z)) (Nat.fromBitsLE (target z)))) HH.symm


theorem coefficient_packet (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (q : List Bool) (u v : ℕ) :
    coefficientWord F negative W p (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((head F negative W p (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (RationalMonomialParameterShift.nativeTargetWidth F W (pairFst q)) u)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q)+1)) :=
  FixedWidthBivariateReboxBits.coefficient_packet (fun c=>F.arity c+1)
    (RationalMonomialParameterShift.nativeTargetWidth F W) (head F negative W p) q u v

noncomputable def reader (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>F.arity c+1) W p))
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars)
    (hfit : ∀ c y,((p c).coeff y).totalDegree<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>F.arity c+1)
      (RationalMonomialParameterShift.nativeTargetWidth F W) (head F negative W p)) :=
  FixedWidthBivariateReader.reader _ _ _ (coefficientWord F negative W p)
    (coefficient_evaluator F negative W p R hA hW hi hw hS hfit) (hA.add (UnaryFn.const 1))
    (RationalMonomialParameterShift.nativeTargetWidth_unary F W hA hW hw)
    (fun c=>RationalMonomialParameterShift.sourceDegree F W c*(F.weight c+1))
    (coefficient_degree F negative W p (fun c y i=>(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (hfit c y)))
    (RationalMonomialParameterShift.target_fit F W) (coefficient_packet F negative W p)

end LeanCanny.Algebra.RationalMonomialBivariateShift
