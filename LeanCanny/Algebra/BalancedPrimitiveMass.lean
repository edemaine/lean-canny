/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableIntegerUniformBounds
public import LeanCanny.Algebra.BalancedPrimitivePolynomials

/-! # Uniform mass and degree envelopes for balanced primitive trees

One bound controls the parameter degree and mass exponent, and every flattened
coordinate degree and mass exponent. A pair step raises it to the fixed power
sixteen, so a tree of height h uses the envelope T^(16^h).
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedPrimitiveTree
open Polynomial UnivariateRational

structure UniformBounds (a : ℕ → SeparableIntegerPolynomial) (h i T : ℕ) : Prop where
  parameterDegree : (node a h i).polynomial.natDegree ≤ T
  parameterMass : coefficientMass (node a h i).polynomial ≤ 2 ^ T
  coordinateDegree : ∀ j, (flat a h i j).degree ≤ T
  numeratorMass : ∀ j, coefficientMass (flat a h i j).numerator ≤ 2 ^ T
  denominatorMass : ∀ j, coefficientMass (flat a h i j).denominator ≤ 2 ^ T

theorem UniformBounds.mono {a : ℕ → SeparableIntegerPolynomial} {h i T U : ℕ}
    (hb : UniformBounds a h i T) (hTU : T ≤ U) : UniformBounds a h i U :=
  ⟨hb.parameterDegree.trans hTU, hb.parameterMass.trans (Nat.pow_le_pow_right (by decide) hTU),
    fun j => (hb.coordinateDegree j).trans hTU,
    fun j => (hb.numeratorMass j).trans (Nat.pow_le_pow_right (by decide) hTU),
    fun j => (hb.denominatorMass j).trans (Nat.pow_le_pow_right (by decide) hTU)⟩

theorem uniform_zero (a : ℕ → SeparableIntegerPolynomial) (i T : ℕ) (hT : 4 ≤ T)
    (hd : (a i).polynomial.natDegree ≤ T) (hm : coefficientMass (a i).polynomial ≤ 2 ^ T) :
    UniformBounds a 0 i T := by
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  refine ⟨hd, hm, ?_, ?_, ?_⟩
  · intro j
    norm_num [flat, identityCoordinate, Coordinate.degree]
    omega
  · intro j
    simpa only [flat, identityCoordinate, hx] using (Nat.one_le_two_pow : 1 ≤ 2 ^ T)
  · intro j
    change coefficientMass (1 : ℤ[X]) ≤ 2 ^ T
    simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using (Nat.one_le_two_pow : 1 ≤ 2 ^ T)

private theorem composition_exponent (T e : ℕ) (hT : 4 ≤ T) (he : e ≤ T) : T + e * T ^ 10 ≤ T ^ 16 := by
  have h1 : T ≤ T ^ 11 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 11 by decide)
  have hm : e * T ^ 10 ≤ T ^ 11 := (Nat.mul_le_mul_right _ he).trans_eq (by ring)
  have h13 : T ^ 13 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hf : 16 * T ^ 11 ≤ T ^ 16 := (CannyResultantBits.sixteen_mul_pow_le T 11 hT).trans h13
  omega

theorem uniform_succ (a : ℕ → SeparableIntegerPolynomial) (h i T : ℕ) (hT : 4 ≤ T)
    (hl : UniformBounds a h (2 * i) T) (hr : UniformBounds a h (2 * i + 1) T) :
    UniformBounds a (h + 1) i (T ^ 16) := by
  have h2 : T ^ 2 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : T ^ 4 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have h10 : T ^ 10 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hm := SeparableIntegerPolynomial.coordinates_mass_uniform (node a h (2 * i)) (node a h (2 * i + 1)) T hT
    hl.parameterDegree hr.parameterDegree hl.parameterMass hr.parameterMass
  have hd := SeparableIntegerPolynomial.coordinates_degree_uniform (node a h (2 * i)) (node a h (2 * i + 1)) T hT
    hl.parameterDegree hr.parameterDegree
  have hf (j : ℕ) : (flat a (h + 1) i j).degree ≤ T ^ 16 ∧
      coefficientMass (flat a (h + 1) i j).numerator ≤ 2 ^ (T ^ 16) ∧
      coefficientMass (flat a (h + 1) i j).denominator ≤ 2 ^ (T ^ 16) := by
    by_cases hj : j < 2 ^ h
    · rw [flat, ite_eq_left hj]
      have hdeg := (Coordinate.comp_degree _ _).trans (Nat.mul_le_mul (hl.coordinateDegree j) hd.1)
      have hmass := Coordinate.comp_mass (flat a h (2 * i) j)
        ((node a h (2 * i)).leftCoordinate (node a h (2 * i + 1))) T (T ^ 10)
        (hl.numeratorMass j) (hl.denominatorMass j) hm.1 hm.2.2
      have hpow := Nat.pow_le_pow_right (n := 2) (by decide) (composition_exponent T _ hT (hl.coordinateDegree j))
      exact ⟨hdeg.trans ((show T * T ^ 3 = T ^ 4 by ring).le.trans h4), hmass.1.trans hpow, hmass.2.trans hpow⟩
    · rw [flat, ite_eq_right hj]
      have hdeg := (Coordinate.comp_degree _ _).trans (Nat.mul_le_mul (hr.coordinateDegree (j - 2 ^ h)) hd.2)
      have hmass := Coordinate.comp_mass (flat a h (2 * i + 1) (j - 2 ^ h))
        ((node a h (2 * i)).rightCoordinate (node a h (2 * i + 1))) T (T ^ 10)
        (hr.numeratorMass _) (hr.denominatorMass _) hm.2.1 hm.2.2
      have hpow := Nat.pow_le_pow_right (n := 2) (by decide) (composition_exponent T _ hT (hr.coordinateDegree (j - 2 ^ h)))
      exact ⟨hdeg.trans ((show T * T ^ 3 = T ^ 4 by ring).le.trans h4), hmass.1.trans hpow, hmass.2.trans hpow⟩
  exact ⟨(SeparableIntegerPolynomial.combine_degree_uniform _ _ T hl.parameterDegree hr.parameterDegree).trans h2,
    (SeparableIntegerPolynomial.combine_mass_uniform _ _ T hT hl.parameterDegree hr.parameterDegree hl.parameterMass hr.parameterMass).trans
      (Nat.pow_le_pow_right (by decide) h10), fun j => (hf j).1, fun j => (hf j).2.1, fun j => (hf j).2.2⟩

theorem uniform_bounds (a : ℕ → SeparableIntegerPolynomial) (T : ℕ) (hT : 4 ≤ T)
    (hd : ∀ i, (a i).polynomial.natDegree ≤ T) (hm : ∀ i, coefficientMass (a i).polynomial ≤ 2 ^ T) (h i : ℕ) :
    UniformBounds a h i (T ^ (16 ^ h)) := by
  induction h generalizing i with
  | zero => simpa only [pow_zero, pow_one] using uniform_zero a i T hT (hd i) (hm i)
  | succ h ih =>
    have ht : T ≤ T ^ (16 ^ h) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 16 ^ h from Nat.one_le_pow _ _ (by decide))
    have hb := uniform_succ a h i (T ^ (16 ^ h)) (hT.trans ht) (ih _) (ih _)
    simpa only [← pow_mul, pow_succ (16 : ℕ) h] using hb

end LeanCanny.Algebra.BalancedPrimitiveTree
