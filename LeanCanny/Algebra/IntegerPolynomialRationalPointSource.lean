/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialExpandSource
public import LeanCanny.Algebra.UnivariateRationalComposition

/-! # Integer polynomial tests at a rational monomial

A bank coordinate has the form a*z^w/b. Clearing an even power of b
preserves its sign. The integer source keeps the outer polynomial implicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialRationalPointSource
open Polynomial
open scoped Classical

structure Scalars where
  numerator : List Bool→ℤ
  denominator : List Bool→ℤ
  mass : List Bool→ℕ
  numerator_bound : ∀ c,(numerator c).natAbs≤2^mass c
  denominator_bound : ∀ c,(denominator c).natAbs≤2^mass c

noncomputable def linear (A : Scalars) (c : List Bool) : Polynomial ℤ := Polynomial.C (A.numerator c)*Polynomial.X
noncomputable def constant (A : Scalars) (c : List Bool) : Polynomial ℤ := Polynomial.C (A.denominator c)

theorem linear_mass (A : Scalars) (c : List Bool) : coefficientMass (linear A c)≤2^A.mass c := by
  unfold linear
  rw [show (Polynomial.X : Polynomial ℤ)=Polynomial.X^1 from (pow_one _).symm,
    Polynomial.C_mul_X_pow_eq_monomial,coefficientMass_monomial]
  exact A.numerator_bound c

noncomputable def clearedSource (S : IntegerPolynomialRootQueriesBits.Source) (A : Scalars) :
    IntegerPolynomialRootQueriesBits.Source where
  polynomial c:=UnivariateRational.clear (2*S.degree c) (S.polynomial c) (linear A c) (constant A c)
  degree c:=2*S.degree c
  mass c:=S.mass c+2*S.degree c*A.mass c
  degree_bound c:=by
    have H:=UnivariateRational.clear_degree (2*S.degree c) (S.polynomial c) (linear A c) (constant A c) 1
      (by simpa only [linear,Polynomial.natDegree_X] using Polynomial.natDegree_C_mul_le (A.numerator c) (Polynomial.X : Polynomial ℤ))
      (by rw [constant,Polynomial.natDegree_C]; omega)
    simpa only [Nat.mul_one] using H
  mass_bound c:=by
    have HD : (S.polynomial c).natDegree≤2*S.degree c:=(S.degree_bound c).trans (by omega)
    have HC : coefficientMass (constant A c)≤2^A.mass c:=by simpa only [constant,coefficientMass_C] using A.denominator_bound c
    calc
      _≤coefficientMass (S.polynomial c)*(2^A.mass c)^(2*S.degree c):=
        UnivariateRational.clear_mass _ _ _ _ HD _ (linear_mass A c) HC
      _≤2^S.mass c*(2^A.mass c)^(2*S.degree c):=Nat.mul_le_mul_right _ (S.mass_bound c)
      _=_:=by rw [←pow_mul,←pow_add]; congr 1; ring

noncomputable def source (S : IntegerPolynomialRootQueriesBits.Source) (A : Scalars) (w : List Bool→ℕ) :=
  IntegerPolynomialExpandSource.source (clearedSource S A) w

theorem eval (S : IntegerPolynomialRootQueriesBits.Source) (A : Scalars) (w : List Bool→ℕ) (c : List Bool)
    (x : ℝ) (hb : A.denominator c≠0) :
    ((source S A w).polynomial c).eval₂ (Int.castRingHom ℝ) x=
      (A.denominator c : ℝ)^(2*S.degree c)*
        (S.polynomial c).eval₂ (Int.castRingHom ℝ) ((A.numerator c : ℝ)*x^w c/(A.denominator c : ℝ)) := by
  rw [source,IntegerPolynomialExpandSource.eval]
  change (UnivariateRational.clear _ _ _ _).eval₂ _ _=_
  rw [UnivariateRational.eval₂_clear (Int.castRingHom ℝ) _ _ _ _
    ((S.degree_bound c).trans (by omega)) (x^w c) (by simpa only [constant,Polynomial.eval₂_C,Int.coe_castRingHom] using (Int.cast_ne_zero.mpr hb : (A.denominator c : ℝ)≠0))]
  simp only [linear,constant,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,Int.coe_castRingHom]

theorem sign (S : IntegerPolynomialRootQueriesBits.Source) (A : Scalars) (w : List Bool→ℕ) (c : List Bool)
    (x : ℝ) (hb : A.denominator c≠0) :
    SignType.sign (((source S A w).polynomial c).eval₂ (Int.castRingHom ℝ) x)=
      SignType.sign ((S.polynomial c).eval₂ (Int.castRingHom ℝ) ((A.numerator c : ℝ)*x^w c/(A.denominator c : ℝ))) := by
  have HP : 0<(A.denominator c : ℝ)^(2*S.degree c) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hb)) _
  rw [eval S A w c x hb,sign_mul,sign_pos HP,one_mul]

end LeanCanny.Algebra.IntegerPolynomialRationalPointSource
