/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformPrimitivePairBounds

/-! # Uniform degree and mass bounds for canonical integer pairs -/

@[expose] public section

namespace LeanCanny.Algebra.SeparableIntegerPolynomial
open Polynomial

theorem select_uniform (p q : SeparableIntegerPolynomial) (T : ℕ)
    (hp : p.polynomial.natDegree ≤ T) (hq : q.polynomial.natDegree ≤ T) :
    PrimitivePair.select p.polynomial q.polynomial ≤ T ^ 4 := by
  have h := (PrimitivePair.select_spec p.polynomial q.polynomial
    (p.separable_in_field (L := AlgebraicClosure ℚ)) (q.separable_in_field (L := AlgebraicClosure ℚ))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).1
  exact h.trans ((Nat.pow_le_pow_left (Nat.mul_le_mul hp hq) 2).trans_eq (by ring))

theorem combine_degree_uniform (p q : SeparableIntegerPolynomial) (T : ℕ)
    (hp : p.polynomial.natDegree ≤ T) (hq : q.polynomial.natDegree ≤ T) :
    (combine p q).polynomial.natDegree ≤ T ^ 2 := by
  rw [combine_degree, pow_two]
  exact Nat.mul_le_mul hp hq

theorem combine_mass_uniform (p q : SeparableIntegerPolynomial) (T : ℕ) (hT : 4 ≤ T)
    (hp : p.polynomial.natDegree ≤ T) (hq : q.polynomial.natDegree ≤ T)
    (hpm : coefficientMass p.polynomial ≤ 2 ^ T) (hqm : coefficientMass q.polynomial ≤ 2 ^ T) :
    coefficientMass (combine p q).polynomial ≤ 2 ^ (T ^ 10) := by
  have hpc (k : ℕ) : (p.polynomial.coeff k).natAbs ≤ 2 ^ T := (coeff_natAbs_le_coefficientMass _ k).trans hpm
  have hqc (k : ℕ) : (q.polynomial.coeff k).natAbs ≤ 2 ^ T := (coeff_natAbs_le_coefficientMass _ k).trans hqm
  have hc (k : ℕ) : (((combine p q).polynomial).coeff k).natAbs ≤ 2 ^ (T ^ 8) :=
    (Nat.size_le.mp ((CannyResultantBits.coefficient_size_le _ _ _ T T (T ^ 4) T T k hp hq
      (select_uniform p q T hp hq) hpc hqc).trans (CannyResultantBits.coefficientBudget_uniform T hT))).le
  have hd : (combine p q).polynomial.natDegree ≤ T * T := by simpa only [pow_two] using combine_degree_uniform p q T hp hq
  exact (coefficientMass_le_pow_of_degree_coeff _ _ _ hd hc).trans
    (Nat.pow_le_pow_right (by decide) (CannyResultantBits.resultantMassExponent_uniform T hT))

theorem coordinates_mass_uniform (p q : SeparableIntegerPolynomial) (T : ℕ) (hT : 4 ≤ T)
    (hp : p.polynomial.natDegree ≤ T) (hq : q.polynomial.natDegree ≤ T)
    (hpm : coefficientMass p.polynomial ≤ 2 ^ T) (hqm : coefficientMass q.polynomial ≤ 2 ^ T) :
    coefficientMass (leftCoordinate p q).numerator ≤ 2 ^ (T ^ 10) ∧
    coefficientMass (rightCoordinate p q).numerator ≤ 2 ^ (T ^ 10) ∧
    coefficientMass (leftCoordinate p q).denominator ≤ 2 ^ (T ^ 10) := by
  have h := PrimitivePair.coordinate_mass p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
    (2 ^ T) (2 ^ T) (fun k => (coeff_natAbs_le_coefficientMass _ k).trans hpm)
    (fun k => (coeff_natAbs_le_coefficientMass _ k).trans hqm)
  have hb := (CannyResultantBits.massBudget_le T T hp hq (select_uniform p q T hp hq)).trans
    (CannyResultantBits.coordinateMassBudget_uniform T hT)
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hb
  exact ⟨h.1.trans hpow, h.2.1.trans hpow, h.2.2.trans hpow⟩

theorem coordinates_degree_uniform (p q : SeparableIntegerPolynomial) (T : ℕ) (hT : 4 ≤ T)
    (hp : p.polynomial.natDegree ≤ T) (hq : q.polynomial.natDegree ≤ T) :
    (leftCoordinate p q).degree ≤ T ^ 3 ∧ (rightCoordinate p q).degree ≤ T ^ 3 := by
  have hs : 4 ≤ T ^ 2 := by simpa using Nat.pow_le_pow_left (show 2 ≤ T by omega) 2
  have hb : T * T + 2 ≤ T ^ 3 := by
    calc
      _ ≤ T ^ 2 * 2 := by rw [pow_two] at *; omega
      _ ≤ T ^ 2 * T := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have hprod := Nat.add_le_add_right (Nat.mul_le_mul hp hq) 2
  exact ⟨(leftCoordinate_degree p q).trans (hprod.trans hb), (rightCoordinate_degree p q).trans (hprod.trans hb)⟩

end LeanCanny.Algebra.SeparableIntegerPolynomial
