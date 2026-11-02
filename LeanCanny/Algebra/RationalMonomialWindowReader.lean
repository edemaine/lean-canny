/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialWindowSpace
public import LeanCanny.Algebra.FixedWidthBivariateReader
/-! # Certified bivariate window readers with native source and queryModulus routing -/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialWindowQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

noncomputable def pull (F : Family) (f : List Bool→List Bool) : Family where
  arity c:=F.arity (f c)
  index c:=F.index (f c)
  weight c:=F.weight (f c)
  scalars := {
    numerator c:=F.scalars.numerator (f c)
    denominator c:=F.scalars.denominator (f c)
    mass c:=F.scalars.mass (f c)
    numerator_bound c:=F.scalars.numerator_bound (f c)
    denominator_bound c:=F.scalars.denominator_bound (f c) }

def queryTarget (z : List Bool) :=pairFst (pairSnd z)
def queryModulus (z : List Bool) :=pairSnd (pairFst z)
def queryOuter (z : List Bool) :=Nat.fromBitsLE (pairSnd (pairSnd z))
def scalarPacket (z : List Bool) :=pair (pair (FixedWidthBivariateReader.origin z) []) (queryModulus z)

noncomputable def coefficientWord (F : Family) (negative : Bool) (W : List Bool→ℕ) : List Bool→List Bool :=
  FixedWidthRowBits.value (fun z=>F.arity (FixedWidthBivariateReader.origin z)+1)
    (W ∘ FixedWidthBivariateReader.origin)
    (fun z=>(query F negative (FixedWidthBivariateReader.origin z)).coeff (queryOuter z)) queryTarget queryModulus

theorem coefficientWord_evaluator (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars) : SpaceFunction (coefficientWord F negative W) :=by
  have ht : queryTarget∈FP:=by polytime [queryTarget]
  have hm : queryModulus∈FP:=by polytime [queryModulus]
  have hy : BinaryFn queryOuter:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hp : scalarPacket∈FP:=by polytime [scalarPacket,queryModulus,FixedWidthBivariateReader.origin]
  have ED : SpaceFunction (fun z=>residueBits
      (F.scalars.denominator (FixedWidthBivariateReader.origin z) : ZMod (Nat.fromBitsLE (queryModulus z)+1))) :=by
    refine (hS.denominator.precompose scalarPacket hp).congr (funext fun z=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [RationalSubstitution.IntegerBits.mValue,scalarPacket,pairSnd_pair])
  have EN : SpaceFunction (fun z=>residueBits
      (F.scalars.numerator (FixedWidthBivariateReader.origin z) : ZMod (Nat.fromBitsLE (queryModulus z)+1))) :=by
    refine (hS.numerator.precompose scalarPacket hp).congr (funext fun z=>?_)
    exact congrArg₂ (fun (a : ℤ) (M : ℕ)=>residueBits (a : ZMod M))
      (by simp only [scalarPacket,RationalSubstitution.IntegerBits.context,pairFst_pair])
      (by simp only [RationalSubstitution.IntegerBits.mValue,scalarPacket,pairSnd_pair])
  have E:=coefficient_evaluator (pull F FixedWidthBivariateReader.origin) negative
    (W ∘ FixedWidthBivariateReader.origin) queryOuter queryTarget queryModulus
    (hA.comp FixedWidthBivariateReader.origin_FP) (hW.comp FixedWidthBivariateReader.origin_FP)
    (hi.comp FixedWidthBivariateReader.origin_FP) (hw.comp FixedWidthBivariateReader.origin_FP)
    hy ht hm ED EN
  refine E.congr (funext fun z=>?_)
  have HE : query (pull F FixedWidthBivariateReader.origin) negative z=
      query F negative (FixedWidthBivariateReader.origin z) :=rfl
  simp only [coefficientWord,FixedWidthRowBits.value]
  rw [HE]
  rfl

private noncomputable def entryAt (F : Family) (negative : Bool) (c : List Bool) (W y u : ℕ) (mw : List Bool) :=
  residueBits (((((query F negative c).coeff y).coeff (nativeExponent (Equiv.refl _) W u)) : ℤ) :
    ZMod (Nat.fromBitsLE mw+1))

private theorem coefficientWord_entry (F : Family) (negative : Bool) (W : List Bool→ℕ) (z : List Bool) :
    coefficientWord F negative W z=entryAt F negative (FixedWidthBivariateReader.origin z)
      (W (FixedWidthBivariateReader.origin z)) (queryOuter z) (Nat.fromBitsLE (queryTarget z)) (queryModulus z) :=rfl

private theorem entryAt_value (F : Family) (negative : Bool) (c : List Bool) (W y u : ℕ) (mw : List Bool) :
    entryAt F negative c W y u mw=residueBits
      (((((query F negative c).coeff y).coeff (nativeExponent (Equiv.refl _) W u)) : ℤ) : ZMod (Nat.fromBitsLE mw+1)) :=rfl

attribute [local irreducible] entryAt

theorem coefficientWord_packet (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (q : List Bool) (u v : ℕ) :
    coefficientWord F negative W (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((query F negative (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (W (pairFst q)) u)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1)) :=by
  rw [coefficientWord_entry,←entryAt_value]
  simp only [FixedWidthBivariateReader.origin,queryOuter,queryTarget,queryModulus,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def reader (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars) (hfit : ∀ c,F.weight c+1<2^W c) :
    CertifiedPolynomial.BivariateReader
      (FixedWidthBivariateReader.polynomial (fun c=>F.arity c+1) W (query F negative)) :=
  FixedWidthBivariateReader.reader (fun c=>F.arity c+1) W (query F negative)
    (coefficientWord F negative W) (coefficientWord_evaluator F negative W hA hW hi hw hS)
    (hA.add (UnaryFn.const 1)) hW (fun c=>F.weight c+1) (coefficient_degree F negative) hfit
    (coefficientWord_packet F negative W)

noncomputable def nativeWidth (F : Family) (c : List Bool) :=(F.weight c+1).size

theorem nativeWidth_unary (F : Family) (hw : BinaryFn F.weight) : UnaryFn (nativeWidth F) :=
  (UnaryFn.length (hw.add (BinaryFn.const 1)).bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

noncomputable def nativeReader (F : Family) (negative : Bool) (hA : UnaryFn F.arity)
    (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars) :
    CertifiedPolynomial.BivariateReader
      (FixedWidthBivariateReader.polynomial (fun c=>F.arity c+1) (nativeWidth F) (query F negative)) :=
  reader F negative (nativeWidth F) hA (nativeWidth_unary F hw) hi hw hS (fun _=>Nat.lt_size_self _)

end LeanCanny.Algebra.RationalMonomialWindowQuery
