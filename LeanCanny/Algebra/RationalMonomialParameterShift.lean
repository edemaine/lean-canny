/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialWindowQuery
public import LeanCanny.Algebra.CommonDenominatorIndexed
public import LeanCanny.Algebra.SelectedPolynomialLift
/-! # Moving the parameter to an actual rational-monomial endpoint

Only the parameter is shifted. The literal old raw tuple is unchanged.
An even common-denominator allowance preserves signs and needs no inverse
in an integer or modular coefficient circuit.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialParameterShift
open Polynomial RationalMonomialWindowQuery
open scoped Classical

noncomputable def base (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c)) ℤ :=
  FixedWidthMonomialBits.polynomial F.arity F.index F.weight F.scalars.numerator c

noncomputable def parameterNumerator (F : Family) (negative : Bool) (c : List Bool) :
    MvPolynomial (Fin (F.arity c+1)) ℤ :=
  MvPolynomial.rename Fin.succ (base F c)+
    if negative then -(MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0)
      else MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0

noncomputable def numerator (F : Family) (negative : Bool) (c : List Bool)
    (i : Fin (F.arity c+1)) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  Fin.cases (parameterNumerator F negative c)
    (fun j=>MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X j.succ) i

noncomputable def clear (F : Family) (negative : Bool) (c : List Bool) (D : ℕ)
    (p : MvPolynomial (Fin (F.arity c+1)) ℤ) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  CommonDenominatorSpecialization.clear (2*D) (F.scalars.denominator c) (numerator F negative c) p

theorem numerator_degree (F : Family) (negative : Bool) (c : List Bool) (i : Fin (F.arity c+1)) :
    (numerator F negative c i).totalDegree≤F.weight c+1 :=by
  have HB : (base F c).totalDegree≤F.weight c :=by
    unfold base FixedWidthMonomialBits.polynomial
    split_ifs
    · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
    · simp
  have HX (j : Fin (F.arity c+1)) :
      (MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X j).totalDegree≤F.weight c+1 :=by
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X];omega)
  refine Fin.cases ?_ (fun j=>?_) i
  · unfold numerator parameterNumerator
    simp only [Fin.cases_zero]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans (HB.trans (Nat.le_succ _))
    · cases negative <;> simpa only [Bool.false_eq_true,ite_true,ite_false,MvPolynomial.totalDegree_neg] using HX 0
  · exact HX j.succ

theorem degree (F : Family) (negative : Bool) (c : List Bool) (D : ℕ)
    (p : MvPolynomial (Fin (F.arity c+1)) ℤ) :
    (clear F negative c D p).totalDegree≤p.totalDegree*(F.weight c+1) :=
  CommonDenominatorSpecialization.degree_mul _ _ _ _ (numerator_degree F negative c) p

theorem numerator_eval (F : Family) (negative : Bool) (c : List Bool)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0)
    (δ : ℝ) (i : Fin (F.arity c+1)) :
    (numerator F negative c i).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z)/(F.scalars.denominator c:ℝ)=
      (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
        if negative then -δ else δ) z : Fin (F.arity c+1)→ℝ) i :=by
  have H : (F.scalars.denominator c:ℝ)≠0:=Int.cast_ne_zero.mpr hb
  have HT : (MvPolynomial.rename Fin.succ (base F c)).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z)=
      (F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c :=by
    rw [MvPolynomial.eval₂_rename]
    simp [base,FixedWidthMonomialBits.polynomial,hi,MvPolynomial.eval₂_monomial]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [numerator,Fin.cases_zero,parameterNumerator,MvPolynomial.eval₂_add,HT,Fin.cons_zero]
    cases negative <;> simp only [ite_true,Bool.false_eq_true,ite_false,MvPolynomial.eval₂_neg,
      MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X,Fin.cons_zero,Int.coe_castRingHom]
    all_goals field_simp [H]
  · simp only [numerator,Fin.cases_succ,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X,
      Int.coe_castRingHom,Fin.cons_succ]
    exact mul_div_cancel_left₀ _ H

theorem eval (F : Family) (negative : Bool) (c : List Bool) (D : ℕ)
    (p : MvPolynomial (Fin (F.arity c+1)) ℤ) (hp : p.totalDegree≤2*D)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (δ : ℝ) :
    (clear F negative c D p).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z)=
      (F.scalars.denominator c:ℝ)^(2*D)*p.eval₂ (Int.castRingHom ℝ)
        (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
          if negative then -δ else δ) z) :=by
  rw [clear,CommonDenominatorSpecialization.eval _ _ _ _ _ hp (Int.cast_ne_zero.mpr hb)]
  congr 1
  apply congrArg (MvPolynomial.eval₂ (Int.castRingHom ℝ) · p)
  funext i
  exact numerator_eval F negative c z hi hb δ i

theorem sign (F : Family) (negative : Bool) (c : List Bool) (D : ℕ)
    (p : MvPolynomial (Fin (F.arity c+1)) ℤ) (hp : p.totalDegree≤2*D)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (δ : ℝ) :
    SignType.sign ((clear F negative c D p).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z))=
      SignType.sign (p.eval₂ (Int.castRingHom ℝ)
        (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
          if negative then -δ else δ) z)) :=by
  rw [eval F negative c D p hp z hi hb δ,sign_mul,
    sign_pos (by rw [pow_mul];exact pow_pos (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hb)) _),one_mul]

end LeanCanny.Algebra.RationalMonomialParameterShift
