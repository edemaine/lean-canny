/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParametricCoordinatePolynomial
public import LeanCanny.CountingHierarchy.RelativeCriticalMass
public import LeanCanny.CountingHierarchy.QuotientParameterDegree
public import LeanCanny.CountingHierarchy.IntegerQuotientMassBounds
public import LeanCanny.CountingHierarchy.BivariateSwapBounds
public import LeanCanny.CountingHierarchy.BivariateCoefficientMass

/-! # Uniform source-only bounds for coordinate candidate polynomials -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra
open scoped Classical

variable {n : ℕ}

def coordinateParameterDegreeBound (n d : ℕ) : ℕ :=
  (d + 1) ^ n * (n + n * ((d + 1) ^ n + n * d))

def coordinateCharacteristicMassExponent (n d b : ℕ) : ℕ :=
  quotientCharMassExponent n d 1 0 (relativeRelationMassExponent d b)

theorem coordinateParameterLower_parameterDegree (d : ℕ) (F : MvPolynomial (Fin n) ℤ) (i : Fin n) :
    HasParameterDegree (coordinateParameterLower d F i) 1 := by
  have hzero : HasParameterDegree
      (MvPolynomial.C (0 : Polynomial ℤ) : MvPolynomial (Fin n) (Polynomial ℤ)) 0 :=
    HasParameterDegree.C _ (by simp)
  have hu : HasParameterDegree
      (MvPolynomial.C Polynomial.X : MvPolynomial (Fin n) (Polynomial ℤ)) 1 :=
    HasParameterDegree.C _ (by simp)
  have h := hzero.sub (hu.mul ((HasParameterDegree.map_C F).pderiv i))
  simpa only [coordinateParameterLower, criticalLower, zero_pow (by omega : d + 1 ≠ 0),
    Nat.add_zero, Nat.max_eq_right (Nat.zero_le 1)] using h

theorem coordinateParameterLower_mass_le (d b : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) (i : Fin n) :
    ParameterMass.mass (coordinateParameterLower d F i) ≤ 2 ^ relativeRelationMassExponent d b := by
  rw [coordinateParameterLower, criticalLower, zero_pow (by omega : d + 1 ≠ 0)]
  apply (ParameterMass.sub_le _ _).trans
  rw [ParameterMass.C, coefficientMass_zero, Nat.zero_add]
  apply (ParameterMass.mul_le _ _).trans
  have hx : coefficientMass (Polynomial.X : Polynomial ℤ) = 1 := by
    simpa only [Polynomial.monomial_one_one_eq_X, Int.natAbs_one] using coefficientMass_monomial 1 (1 : ℤ)
  rw [ParameterMass.C, hx, Nat.one_mul]
  apply (ParameterMass.pderiv_le _ _).trans
  apply (Nat.mul_le_mul ((map_degree_le _ _).trans hF) (by simpa only [ParameterMass.map_C] using hM)).trans
  calc
    (d + 1) * 2 ^ b ≤ 2 ^ (d + 1).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = 2 ^ ((d + 1).size + b) := (pow_add 2 _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold relativeRelationMassExponent; omega)

theorem parametricCoordinatePolynomial_coefficient_degree_le (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) (k : ℕ) :
    ((parametricCoordinatePolynomial d F hF i).coeff k).natDegree ≤ coordinateParameterDegreeBound n d := by
  have hr (j : Fin n) : (coordinateParameterLower d F j).totalDegree ≤ d := by
    have := coordinateParameterLower_degree d F hF j
    omega
  have h := multiplicationMatrix_charpoly_parameterDegree_le d hd (coordinateParameterLower d F)
    hr (MvPolynomial.X i) 1 1 0 (by simp) (coordinateParameterLower_parameterDegree d F)
    (HasParameterDegree.X i) k
  simpa only [parametricCoordinatePolynomial, coordinateParameterDegreeBound, Nat.mul_zero, Nat.zero_add, Nat.mul_one] using h

theorem parametricCoordinatePolynomial_mass_le (d b : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) (i : Fin n) :
    NestedMass.mass (parametricCoordinatePolynomial d F hF i) ≤
      2 ^ coordinateCharacteristicMassExponent n d b := by
  have hr (j : Fin n) : (coordinateParameterLower d F j).totalDegree ≤ d := by
    have := coordinateParameterLower_degree d F hF j
    omega
  exact multiplicationMatrix_charpoly_nestedMass_le d hd (coordinateParameterLower d F) hr
    (MvPolynomial.X i) 1 0 (relativeRelationMassExponent d b) (by simp)
    (by simp only [ParameterMass.X, pow_zero, le_refl]) (coordinateParameterLower_mass_le d b F hF hM)

theorem coordinateCandidate_degree_le (d : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) (j : ℕ) :
    ((Bivariate.swap (parametricCoordinatePolynomial d F hF i)).coeff j).natDegree ≤ (d + 1) ^ n :=
  (bivariate_swap_coefficient_degree_le _ j).trans_eq (parametricCoordinatePolynomial_natDegree d F hF i)

theorem coordinateCandidate_mass_le (d b : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b)
    (i : Fin n) (j : ℕ) :
    coefficientMass ((Bivariate.swap (parametricCoordinatePolynomial d F hF i)).coeff j) ≤
      2 ^ coordinateCharacteristicMassExponent n d b :=
  (bivariate_swap_coefficient_mass_le _ j).trans (parametricCoordinatePolynomial_mass_le d b hd F hF hM i)

theorem coordinateCandidate_index_bound (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (i : Fin n) :
    (Bivariate.swap (parametricCoordinatePolynomial d F hF i)).natDegree ≤ coordinateParameterDegreeBound n d :=
  bivariate_swap_degree_le _ _ (parametricCoordinatePolynomial_coefficient_degree_le d hd F hF i)

end LeanCanny.CountingHierarchy
