/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthMonomialSpace
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSource
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Positive-cleared window queries at one actual rational monomial

The retained coordinate is numerator*z_i^weight/denominator. Squaring the
common denominator preserves every sign, including negative denominators.
The window parameter is an independent head variable; the old tuple is literal.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialWindowQuery
open Polynomial
open scoped Classical

structure Family where
  arity : List Bool→ℕ
  index : List Bool→ℕ
  weight : List Bool→ℕ
  scalars : IntegerPolynomialRationalPointSource.Scalars

noncomputable def raw (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c)) ℤ :=
  FixedWidthMonomialBits.polynomial F.arity F.index F.weight
    (fun c=>F.scalars.denominator c*F.scalars.numerator c) c
noncomputable def epsilon (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  MvPolynomial.C (F.scalars.denominator c^2)*MvPolynomial.X 0
noncomputable def body (F : Family) (negative : Bool) (c : List Bool) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  (if negative then -epsilon F c else epsilon F c)-MvPolynomial.rename Fin.succ (raw F c)
noncomputable def query (F : Family) (negative : Bool) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ) :=
  Polynomial.C (MvPolynomial.C (F.scalars.denominator c^2))*Polynomial.X+Polynomial.C (body F negative c)

theorem coefficient (F : Family) (negative : Bool) (c : List Bool) (y : ℕ) :
    (query F negative c).coeff y=if y=1 then MvPolynomial.C (F.scalars.denominator c^2)
      else if y=0 then body F negative c else 0 :=by
  unfold query
  rw [Polynomial.coeff_add,Polynomial.coeff_C_mul]
  by_cases h1 : y=1
  · subst y
    simp only [Polynomial.coeff_X_one,Polynomial.coeff_C,one_ne_zero,ite_false,mul_one,add_zero,ite_true]
  · by_cases h0 : y=0
    · subst y
      simp only [Polynomial.coeff_X_zero,Polynomial.coeff_C,ite_true,zero_ne_one,ite_false,mul_zero,zero_add]
    · rw [Polynomial.coeff_X_of_ne_one h1,Polynomial.coeff_C]
      simp only [h1,h0,ite_false,mul_zero,add_zero]

theorem degree (F : Family) (negative : Bool) (c : List Bool) : (query F negative c).natDegree≤1 :=by
  unfold query
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  · rw [Polynomial.natDegree_C]
    omega

theorem epsilon_degree (F : Family) (c : List Bool) : (epsilon F c).totalDegree≤1 :=by
  unfold epsilon
  exact (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X])

theorem raw_degree (F : Family) (c : List Bool) : (raw F c).totalDegree≤F.weight c :=by
  unfold raw FixedWidthMonomialBits.polynomial
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

theorem coefficient_degree (F : Family) (negative : Bool) (c : List Bool) (y : ℕ) :
    ((query F negative c).coeff y).totalDegree≤F.weight c+1 :=by
  have HE : (epsilon F c).totalDegree≤F.weight c+1 :=(epsilon_degree F c).trans (by omega)
  rw [coefficient]
  split_ifs
  · rw [MvPolynomial.totalDegree_C]
    omega
  · unfold body
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,MvPolynomial.totalDegree_neg] using HE
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans ((raw_degree F c).trans (Nat.le_succ _))
  · simp

theorem raw_mass (F : Family) (c : List Bool) : MvMass.mass (raw F c)≤2^(2*F.scalars.mass c) :=by
  unfold raw FixedWidthMonomialBits.polynomial
  split_ifs
  · rw [MvMass.monomial,Int.natAbs_mul]
    exact (Nat.mul_le_mul (F.scalars.denominator_bound c) (F.scalars.numerator_bound c)).trans_eq
      (by rw [←pow_add,two_mul])
  · simp

theorem epsilon_mass (F : Family) (c : List Bool) : MvMass.mass (epsilon F c)≤2^(2*F.scalars.mass c) :=by
  unfold epsilon
  apply (MvMass.mul_le _ _).trans
  simp only [MvMass.C,MvMass.X,Nat.mul_one,Int.natAbs_pow]
  exact (Nat.pow_le_pow_left (F.scalars.denominator_bound c) 2).trans_eq (by rw [←pow_mul,Nat.mul_comm])

theorem coefficient_mass (F : Family) (negative : Bool) (c : List Bool) (y : ℕ) :
    MvMass.mass ((query F negative c).coeff y)≤2^(2*F.scalars.mass c+1) :=by
  rw [coefficient]
  split_ifs
  · rw [MvMass.C,Int.natAbs_pow]
    exact ((Nat.pow_le_pow_left (F.scalars.denominator_bound c) 2).trans_eq
      (by rw [←pow_mul,Nat.mul_comm])).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  · have HE : MvMass.mass (if negative then -epsilon F c else epsilon F c)≤2^(2*F.scalars.mass c) :=by
      cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,MvMass.neg] using epsilon_mass F c
    have H:=(MvMass.sub_le (if negative then -epsilon F c else epsilon F c)
      (MvPolynomial.rename Fin.succ (raw F c))).trans
      (Nat.add_le_add HE ((MvMass.rename_le Fin.succ (raw F c)).trans (raw_mass F c)))
    exact H.trans_eq (by rw [pow_succ]; omega)
  · simp

end LeanCanny.Algebra.RationalMonomialWindowQuery
