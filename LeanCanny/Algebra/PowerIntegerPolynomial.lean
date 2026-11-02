/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace

/-! # Degree-one integer leaves for signed powers of two

An exponent is retained as binary metadata. The expanded constant need not
be written as an original term or stored as a binary integer.
-/
@[expose] public section
namespace LeanCanny.Algebra.PowerIntegerPolynomial
open Polynomial
open scoped Classical

noncomputable def value (negative : Prop) (E : ℕ) : ℤ := if negative then -(2^E) else 2^E
noncomputable def polynomial (negative : Prop) (E : ℕ) : Polynomial ℤ := Polynomial.X-Polynomial.C (value negative E)

theorem value_ne_zero (negative : Prop) (E : ℕ) : value negative E≠0 := by
  unfold value
  split_ifs <;> exact (by simpa only [neg_ne_zero] using pow_ne_zero E (by decide : (2 : ℤ)≠0))

theorem value_abs (negative : Prop) (E : ℕ) : (value negative E).natAbs=2^E := by
  unfold value
  split_ifs <;> simp only [Int.natAbs_neg,Int.natAbs_pow,show (2 : ℤ).natAbs=2 from rfl]

theorem degree (negative : Prop) (E : ℕ) : (polynomial negative E).natDegree=1 := natDegree_X_sub_C _
theorem leading (negative : Prop) (E : ℕ) : (polynomial negative E).leadingCoeff=1 := (monic_X_sub_C _).leadingCoeff

theorem coefficient (negative : Prop) (E k : ℕ) :
    (polynomial negative E).coeff k=if k=1 then 1 else if k=0 then -value negative E else 0 := by
  simp only [polynomial,coeff_sub,coeff_X,coeff_C]
  split_ifs <;> omega

theorem mass (negative : Prop) (E : ℕ) : coefficientMass (polynomial negative E)≤2^(E+1) := by
  have H:=(coefficientMass_sub_le Polynomial.X (Polynomial.C (value negative E)))
  have HX : coefficientMass (Polynomial.X : Polynomial ℤ)=1 := by simp [coefficientMass]
  simp only [HX,coefficientMass_C,value_abs] at H
  have HP:=Nat.one_le_two_pow (n:=E)
  rw [pow_succ]
  exact H.trans (by omega)

theorem root_iff (negative : Prop) (E : ℕ) (a : ℝ) :
    (polynomial negative E).eval₂ (Int.castRingHom ℝ) a=0↔a=(value negative E : ℝ) := by
  simp only [polynomial,eval₂_sub,eval₂_X,eval₂_C,Int.coe_castRingHom,sub_eq_zero]

noncomputable def source (negative : List Bool→Prop) (exponent : List Bool→ℕ) : IntegerPolynomialRootQueriesBits.Source where
  polynomial q:=polynomial (negative q) (exponent q)
  degree _:=1
  mass q:=exponent q+1
  degree_bound _q:=(degree _ _).le
  mass_bound _q:=mass _ _

end LeanCanny.Algebra.PowerIntegerPolynomial
