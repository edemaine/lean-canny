/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialParameterShiftSpace
public import LeanCanny.Algebra.FixedWidthKroneckerSpace
public import LeanCanny.Algebra.FixedWidthCommonDenominatorSpace
public import LeanCanny.Algebra.RationalMonomialWindowReader
/-! # Charged native denominator-cleared parameter substitution

The original integer-MV source reader remains charged. Every coordinate
numerator is reconstructed from the same two scalar readers and binary
metadata; no substituted polynomial is stored.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialParameterShift
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open RationalMonomialWindowQuery
open RationalSubstitution.IntegerBits (context mValue context_mem_FP)
open scoped Classical

def coordinateIndex (q : List Bool) :=Nat.fromBitsLE (pairFst (pairSnd (pairFst q)))
def coordinateTarget (q : List Bool) :=pairSnd (pairSnd (pairFst q))
def scalarQuery (q : List Bool) :=pair (pair (context q) []) (pairSnd q)

noncomputable def numeratorValue (F : Family) (negative : Bool) (V : List Bool→ℕ) :=
  FixedWidthKroneckerBits.value (fun q=>(pull F context).arity q+1) (V ∘ context)
    (fun q=>numeratorAt (pull F context) negative q (coordinateIndex q)) coordinateTarget pairSnd

theorem numerator_evaluator (F : Family) (negative : Bool) (V : List Bool→ℕ)
    (hA : UnaryFn F.arity) (hV : UnaryFn V) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars) (hfit : ∀ c,F.weight c+1<2^V c) :
    SpaceFunction (numeratorValue F negative V) :=by
  have hidx : BinaryFn coordinateIndex:=BinaryFn.fromBits
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
  have ht : coordinateTarget∈FP:=by polytime [coordinateTarget]
  have hs : scalarQuery∈FP:=by polytime [scalarQuery,RationalSubstitution.IntegerBits.context]
  have ED : SpaceFunction (fun q=>residueBits
      (F.scalars.denominator (context q) : ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=by
    refine (hS.denominator.precompose scalarQuery hs).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarQuery,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [RationalSubstitution.IntegerBits.mValue,scalarQuery,pairSnd_pair])
  have EN : SpaceFunction (fun q=>residueBits
      (F.scalars.numerator (context q) : ZMod (Nat.fromBitsLE (pairSnd q)+1))) :=by
    refine (hS.numerator.precompose scalarQuery hs).congr (funext fun q=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarQuery,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [RationalSubstitution.IntegerBits.mValue,scalarQuery,pairSnd_pair])
  have E:=coefficient_evaluator (pull F context) negative (V ∘ context) coordinateIndex coordinateTarget pairSnd
    (hA.comp context_mem_FP) (hV.comp context_mem_FP) (hi.comp context_mem_FP) (hw.comp context_mem_FP)
    hidx ht pairSnd_mem_FP ED EN
  exact FixedWidthKroneckerBits.evaluator _ _ (fun q=>F.weight (context q)+1) _ _ _
    ((hA.comp context_mem_FP).add (UnaryFn.const 1)) (hV.comp context_mem_FP) ht
    (fun q=>numeratorAt_degree (pull F context) negative q (coordinateIndex q)) (fun q=>hfit (context q)) E

private noncomputable def numeratorEntry (F : Family) (negative : Bool) (c : List Bool) (V i k : ℕ) (mw : List Bool) :=
  residueBits ((((FixedWidthKronecker.encode (F.arity c+1) V (numeratorAt F negative c i)).coeff k) : ℤ) :
    ZMod (Nat.fromBitsLE mw+1))

private theorem numeratorValue_entry (F : Family) (negative : Bool) (V : List Bool→ℕ) (q : List Bool) :
    numeratorValue F negative V q=numeratorEntry F negative (context q) (V (context q))
      (coordinateIndex q) (Nat.fromBitsLE (coordinateTarget q)) (pairSnd q) :=rfl

private theorem numeratorEntry_value (F : Family) (negative : Bool) (c : List Bool) (V i k : ℕ) (mw : List Bool) :
    numeratorEntry F negative c V i k mw=residueBits
      ((((FixedWidthKronecker.encode (F.arity c+1) V (numeratorAt F negative c i)).coeff k) : ℤ) :
        ZMod (Nat.fromBitsLE mw+1)) :=rfl

attribute [local irreducible] numeratorEntry

theorem numerator_packet (F : Family) (negative : Bool) (V : List Bool→ℕ) (c : List Bool) (i k m : ℕ) (hm : 0<m) :
    numeratorValue F negative V
      (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m-1)))=
    residueBits ((((FixedWidthKronecker.encode (F.arity c+1) (V c) (numeratorAt F negative c i)).coeff k) : ℤ) : ZMod m) :=by
  rw [numeratorValue_entry]
  have HE:=numeratorEntry_value F negative c (V c) i k (BinaryNatCode.encode (m-1))
  have HM : Nat.fromBitsLE (BinaryNatCode.encode (m-1))+1=m:=by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits];omega
  rw [HM] at HE
  rw [←HE]
  simp only [RationalSubstitution.IntegerBits.context,coordinateIndex,coordinateTarget,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def scalarValue (F : Family) (q : List Bool) :=
  residueBits (F.scalars.denominator (pairFst q) : ZMod (Nat.fromBitsLE (pairSnd q)+1))

theorem scalar_evaluator (F : Family) (hS : IntegerPolynomialRationalPointSource.Access F.scalars) :
    SpaceFunction (scalarValue F) :=by
  let f (q : List Bool) :=pair (pair (pairFst q) []) (pairSnd q)
  have hf : f∈FP:=by polytime [f]
  refine (hS.denominator.precompose f hf).congr (funext fun q=>?_)
  exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
    (by simp only [f,RationalSubstitution.IntegerBits.context,pairFst_pair])
    (by simp only [RationalSubstitution.IntegerBits.mValue,f,pairSnd_pair])

noncomputable def sourceFamily (F : Family) (negative : Bool) (W V : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c) : FixedWidthCommonDenominatorBits.Family where
  sourceArity c:=F.arity c+1
  sourceWidth:=W
  targetArity c:=F.arity c+1
  targetWidth:=V
  source:=p
  denominator:=F.scalars.denominator
  numerator c i:=numeratorAt F negative c i
  source_fit:=hfit

theorem sourceFamily_polynomial (F : Family) (negative : Bool) (W V : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ) (hfit : ∀ c i,(p c).degreeOf i<2^W c)
    (c : List Bool) :
    (sourceFamily F negative W V p hfit).polynomial c=
      clear F negative c ((F.arity c+1)*2^W c) (p c) :=by
  unfold FixedWidthCommonDenominatorBits.Family.polynomial clear
  have HN : (fun i : Fin (F.arity c+1)=>numeratorAt F negative c i.val)=numerator F negative c :=
    funext (numeratorAt_eq F negative c)
  simp only [sourceFamily,FixedWidthCommonDenominatorBits.Family.allowance]
  rw [HN,show (F.arity c+1)*(2*2^W c)=2*((F.arity c+1)*2^W c) by ring]
  rfl

noncomputable def access (F : Family) (negative : Bool) (W V : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ) (hfit : ∀ c i,(p c).degreeOf i<2^W c)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hV : UnaryFn V) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars) (hnum : ∀ c,F.weight c+1<2^V c)
    (source : List Bool→List Bool) (S : SpaceFunction source)
    (hs : ∀ c r,r<(sourceFamily F negative W V p hfit).univariate.terms c→∀ m,0<m→
      source (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m-1)))=
        residueBits (((sourceFamily F negative W V p hfit).univariate.coefficient c r : ℤ) : ZMod m)) :
    FixedWidthRationalSubstitutionBits.Access (sourceFamily F negative W V p hfit).univariate :=
  FixedWidthCommonDenominatorBits.access (sourceFamily F negative W V p hfit)
    (hA.add (UnaryFn.const 1)) hW source (numeratorValue F negative V) (scalarValue F) S
    (numerator_evaluator F negative V hA hV hi hw hS hnum) (scalar_evaluator F hS) hs
    (fun c i _ k m hm=>numerator_packet F negative V c i k m hm)
    (by
      intro c m hm
      apply congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      · simp only [pairFst_pair]
        rfl
      · simp only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
        omega)

end LeanCanny.Algebra.RationalMonomialParameterShift
