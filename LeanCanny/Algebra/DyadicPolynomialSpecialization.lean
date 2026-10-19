/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicSpecialization
public import LeanCanny.Algebra.CoefficientMass

/-! # Coefficientwise dyadic specialization of parameterized polynomials

The outer polynomial variable is retained. A uniform inner degree clears every
parameter denominator by the same positive factor.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicPolynomial
open Polynomial
open scoped BigOperators

noncomputable def specialize (p : (ℤ[X])[X]) (D s : ℕ) : ℤ[X] :=
  p.sum fun i a => monomial i (DyadicSpecialization.numerator a D s)

theorem coeff_specialize (p : (ℤ[X])[X]) (D s i : ℕ) :
    (specialize p D s).coeff i = DyadicSpecialization.numerator (p.coeff i) D s := by
  classical
  by_cases hi : i ∈ p.support
  · simp [specialize, Polynomial.sum, Polynomial.coeff_monomial, hi]
  · have hz : p.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    simp [specialize, Polynomial.sum, Polynomial.coeff_monomial, hi, hz]

@[simp] theorem specialize_zero (D s : ℕ) : specialize 0 D s = 0 := by
  ext i
  simp only [coeff_specialize, Polynomial.coeff_zero, DyadicSpecialization.numerator_zero]

theorem natDegree_le (p : (ℤ[X])[X]) (D s : ℕ) : (specialize p D s).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_specialize, Polynomial.coeff_eq_zero_of_natDegree_lt hi, DyadicSpecialization.numerator_zero]

noncomputable def evalHom (s : ℕ) : ℤ[X] →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) (InfinitesimalSign.dyadic s)

theorem map_specialize (p : (ℤ[X])[X]) (D s : ℕ) (hD : ∀ i, (p.coeff i).natDegree ≤ D) :
    (specialize p D s).map (Int.castRingHom ℝ) =
      C ((2 : ℝ) ^ (s * D)) * p.map (evalHom s) := by
  ext i
  rw [Polynomial.coeff_map, coeff_specialize, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  exact DyadicSpecialization.numerator_eval (p.coeff i) D s (hD i)

theorem numerator_eq_zero_iff (p : ℤ[X]) (D s b : ℕ) (hD : p.natDegree ≤ D)
    (hm : coefficientMass p ≤ 2 ^ b) (hs : b < s) : DyadicSpecialization.numerator p D s = 0 ↔ p = 0 := by
  constructor
  · intro hz
    have h := DyadicSpecialization.numerator_sign p D s b hD hm hs
    rw [hz, sign_zero] at h
    exact Polynomial.trailingCoeff_eq_zero.mp (sign_eq_zero_iff.mp h.symm)
  · intro hz
    rw [hz, DyadicSpecialization.numerator_zero]

theorem natDegree_eq (p : (ℤ[X])[X]) (D s b : ℕ) (hD : ∀ i, (p.coeff i).natDegree ≤ D)
    (hm : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ b) (hs : b < s) :
    (specialize p D s).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · have hl : p.coeff p.natDegree ≠ 0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hp
    have hc : (specialize p D s).coeff p.natDegree ≠ 0 := by
      rw [coeff_specialize]
      exact (numerator_eq_zero_iff _ _ _ _ (hD _) (hm _) hs).not.mpr hl
    exact le_antisymm (natDegree_le p D s) (Polynomial.le_natDegree_of_ne_zero hc)

theorem coeff_abs_le (p : (ℤ[X])[X]) (D s b : ℕ) (hD : ∀ i, (p.coeff i).natDegree ≤ D)
    (hm : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ b) (i : ℕ) :
    ((specialize p D s).coeff i).natAbs ≤ 2 ^ (b + s * D) := by
  rw [coeff_specialize]
  have h := (DyadicSpecialization.numerator_abs_le (p.coeff i) D s (hD i)).trans
    (Nat.mul_le_mul_right _ (hm i))
  simpa only [← pow_add] using h

theorem mass_le (p : (ℤ[X])[X]) (D s b N : ℕ) (hN : p.natDegree ≤ N)
    (hD : ∀ i, (p.coeff i).natDegree ≤ D) (hm : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ b) :
    coefficientMass (specialize p D s) ≤ 2 ^ (b + s * D + (N + 1).size) :=
  coefficientMass_le_pow_of_degree_coeff _ _ _ ((natDegree_le p D s).trans hN) (coeff_abs_le p D s b hD hm)

end LeanCanny.Algebra.DyadicPolynomial
