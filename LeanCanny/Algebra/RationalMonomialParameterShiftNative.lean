/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialParameterShiftBounds
/-! # Native substitution with a width derived from original input metadata -/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialParameterShift
open LeanCanny.Encoding LeanCanny.Computation MatrixPower RationalMonomialWindowQuery
open scoped Classical

noncomputable def nativeFamily (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c) :=
  sourceFamily F negative W (nativeTargetWidth F W) p hfit

theorem evaluator (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hi : BinaryFn F.index) (hw : BinaryFn F.weight)
    (hS : IntegerPolynomialRationalPointSource.Access F.scalars)
    (source : List Bool→List Bool) (S : SpaceFunction source)
    (hs : ∀ c r,r<(nativeFamily F negative W p hfit).univariate.terms c→∀ m,0<m→
      source (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m-1)))=
        residueBits (((nativeFamily F negative W p hfit).univariate.coefficient c r : ℤ) : ZMod m))
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>F.arity c+1) (nativeTargetWidth F W)
      (nativeFamily F negative W p hfit).polynomial target modulus) :=by
  let G:=nativeFamily F negative W p hfit
  have hV:=nativeTargetWidth_unary F W hA hW hw
  let A:=access F negative W (nativeTargetWidth F W) p hfit hA hW hV hi hw hS
    (numerator_fit F W) source S hs
  have HF:=G.support_fit (sourceDegree F W) (fun c=>F.weight c+1)
    (source_degree F W p hfit) (fun c i=>numeratorAt_degree F negative c i) (target_fit F W)
  exact FixedWidthCommonDenominatorBits.evaluator G A target modulus (hA.add (UnaryFn.const 1)) hV ht hm HF

theorem native_eval (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c) (c : List Bool)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (δ : ℝ) :
    ((nativeFamily F negative W p hfit).polynomial c).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z)=
      (F.scalars.denominator c:ℝ)^(2*sourceDegree F W c)*(p c).eval₂ (Int.castRingHom ℝ)
        (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
          if negative then -δ else δ) z) :=by
  unfold nativeFamily
  rw [sourceFamily_polynomial]
  exact eval F negative c _ _ ((source_degree F W p hfit c).trans (by dsimp [sourceDegree];omega)) z hi hb δ

theorem native_sign (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c) (c : List Bool)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (δ : ℝ) :
    SignType.sign (((nativeFamily F negative W p hfit).polynomial c).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z))=
      SignType.sign ((p c).eval₂ (Int.castRingHom ℝ)
        (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
          if negative then -δ else δ) z)) :=by
  unfold nativeFamily
  rw [sourceFamily_polynomial]
  exact sign F negative c _ _ ((source_degree F W p hfit c).trans (by dsimp [sourceDegree];omega)) z hi hb δ

end LeanCanny.Algebra.RationalMonomialParameterShift
