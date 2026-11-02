/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialWindowQuery
public import Mathlib.Algebra.Order.Ring.Defs
/-! # Literal same-tuple semantics of positive-cleared window queries -/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialWindowQuery
open Polynomial
open scoped Classical

theorem raw_eval (F : Family) (c : List Bool) (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) :
    (raw F c).eval₂ (Int.castRingHom ℝ) z=
      (F.scalars.denominator c : ℝ)*(F.scalars.numerator c : ℝ)*z ⟨F.index c,hi⟩^F.weight c :=by
  simp [raw,FixedWidthMonomialBits.polynomial,hi,MvPolynomial.eval₂_monomial]

theorem eval_query (F : Family) (negative : Bool) (c : List Bool) (z : Fin (F.arity c)→ℝ)
    (hi : F.index c<F.arity c) (ε u : ℝ) :
    (query F negative c).eval₂ (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) u=
      (F.scalars.denominator c : ℝ)^2*u+
        (if negative then -(F.scalars.denominator c : ℝ)^2*ε else (F.scalars.denominator c : ℝ)^2*ε)-
        (F.scalars.denominator c : ℝ)*(F.scalars.numerator c : ℝ)*z ⟨F.index c,hi⟩^F.weight c :=by
  have HT : (MvPolynomial.rename Fin.succ (raw F c)).eval₂ (Int.castRingHom ℝ) (Fin.cons ε z)=
      (raw F c).eval₂ (Int.castRingHom ℝ) z :=by
    rw [MvPolynomial.eval₂_rename]
    rfl
  simp only [query,Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,
    MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C,Int.coe_castRingHom,Int.cast_pow,body,
    MvPolynomial.eval₂_sub,HT,raw_eval F c z hi]
  have HI : MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.cons ε z)
      (F.scalars.denominator c : MvPolynomial (Fin (F.arity c+1)) ℤ)=
        (F.scalars.denominator c : ℝ) :=map_intCast (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) _
  cases negative <;> simp [epsilon,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval₂_pow,HI] <;> ring

theorem eval_cleared (F : Family) (negative : Bool) (c : List Bool) (z : Fin (F.arity c)→ℝ)
    (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (ε u : ℝ) :
    (query F negative c).eval₂ (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) u=
      (F.scalars.denominator c : ℝ)^2*
        (u-(F.scalars.numerator c : ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c : ℝ)+
          if negative then -ε else ε) :=by
  rw [eval_query F negative c z hi ε u]
  have H : (F.scalars.denominator c : ℝ)≠0:=Int.cast_ne_zero.mpr hb
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals field_simp [H]
  all_goals ring

theorem sign_query (F : Family) (negative : Bool) (c : List Bool) (z : Fin (F.arity c)→ℝ)
    (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (ε u : ℝ) :
    SignType.sign ((query F negative c).eval₂ (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) u)=
      SignType.sign (u-(F.scalars.numerator c : ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c : ℝ)+
        if negative then -ε else ε) :=by
  rw [eval_cleared F negative c z hi hb ε u,sign_mul,
    sign_pos (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hb)),one_mul]

end LeanCanny.Algebra.RationalMonomialWindowQuery
