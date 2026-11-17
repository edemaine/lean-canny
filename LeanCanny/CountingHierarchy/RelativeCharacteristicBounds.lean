/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCriticalMass
public import LeanCanny.CountingHierarchy.ParameterPolynomialFlattening

/-! # Source-only budgets for the relative critical-value polynomial -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue LeanCanny.Algebra
open scoped Classical

variable {n : ℕ} {κ : Type*}

def relativeNumeratorDegreeBound (n d : ℕ) : ℕ := (d + 1) ^ n * (d + 2) + n * d

def relativeCharacteristicParameterDegreeBound (n d : ℕ) : ℕ :=
  (d + 1) ^ n * ((d + 1) ^ n * (d + 2) + n * (d + 2) +
    n * (relativeNumeratorDegreeBound n d * (d + 2)))

def relativeCharacteristicMassExponent (n d b : ℕ) : ℕ :=
  traceMassExponent n (relativeNumeratorDegreeBound n d) ((d + 1) ^ n)
    (relativeObjectiveMassExponent n d b) (relativeRelationMassExponent d b)
    (n.size * n + n * ((d + 1).size + relativeRelationMassExponent d b + 1)) * (d + 1) ^ n +
      ((d + 1) ^ n + 1).size

theorem relativeCharacteristic_coefficient_degree_le (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) (k : ℕ) :
    ((relativeCharacteristic d F hF).coeff k).totalDegree ≤ relativeCharacteristicParameterDegreeBound n d := by
  have hr (i : Fin n) : (relativeLower d F i).totalDegree ≤ d := by
    have := relativeLower_mainDegree d F hF i
    omega
  exact PurePowerResidue.MultivariateParameters.multiplicationMatrix_charpoly_parameterDegree_le
    d hd (relativeLower d F) hr (relativeObjective d F) (d + 2) (d + 2) (d + 2)
    (relativeObjective_mainDegree d F hF) (relativeLower_parameterDegree d (d + 1) F hF)
    (relativeObjective_parameterDegree d (d + 1) F hF) k

theorem relativeCharacteristic_mass_le (d b : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) :
    PolynomialParameterMass.mass (relativeCharacteristic d F hF) ≤ 2 ^ relativeCharacteristicMassExponent n d b := by
  have hr (i : Fin n) : (relativeLower d F i).totalDegree ≤ d := by
    have := relativeLower_mainDegree d F hF i
    omega
  exact PurePowerResidue.MultivariateParameters.multiplicationMatrix_charpoly_nestedMass_le
    d hd (relativeLower d F) hr (relativeObjective d F) (d + 2)
    (relativeObjectiveMassExponent n d b) (relativeRelationMassExponent d b)
    (relativeObjective_mainDegree d F hF) (relativeObjective_mass_le d b F hM)
    (relativeLower_mass_le d b F hF hM)

noncomputable def flattenedRelativeCharacteristic (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) : MvPolynomial (Option (Option κ)) ℤ :=
  flattenParameterPolynomial (relativeCharacteristic d F hF)

theorem flattenedRelativeCharacteristic_degree_le (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) :
    (flattenedRelativeCharacteristic d F hF).totalDegree ≤
      (d + 1) ^ n + relativeCharacteristicParameterDegreeBound n d :=
  flattenParameterPolynomial_degree_le _ _ _ (relativeCharacteristic_natDegree d F hF).le
    (relativeCharacteristic_coefficient_degree_le d hd F hF)

theorem flattenedRelativeCharacteristic_mass_le (d b : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n ⊕ κ) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b) :
    MvMass.mass (flattenedRelativeCharacteristic d F hF) ≤ 2 ^ relativeCharacteristicMassExponent n d b :=
  (flattenParameterPolynomial_mass_le _).trans (relativeCharacteristic_mass_le d b hd F hF hM)

end LeanCanny.CountingHierarchy
