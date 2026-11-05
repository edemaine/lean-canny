/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryEnergyMass
public import LeanCanny.Algebra.CoerciveBoxBounds
public import LeanCanny.Algebra.IntegerPolynomialDyadicInterpolation
/-! # Original-source bounds for the fixed boundary Gram family

Exact integer specializations of the same Gram determinant have certified
native mass bounds. Their dyadic growth bounds each original parameter
coefficient by scalar interpolation; vanishing at every dyadic value also
retains the native target-degree bound before specialization.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryGramMass
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def dimension (n D : ℕ) : ℕ := CoerciveBoxGramEliminant.blockDimension (n+2) (ParameterizedBoundaryGramValues.degreeBound D)
def slope (n D : ℕ) : ℕ := 8 * dimension n D
def offset (n D b : ℕ) : ℕ := CoerciveBoxGramEliminant.massExponent (n+2)
  (ParameterizedBoundaryGramValues.degreeBound D) (ParameterizedBoundaryEnergyMass.energyOffset n D b)
def coefficientBits (n D b : ℕ) : ℕ := IntegerPolynomialDyadic.massBudget 0 (slope n D) (offset n D b)
def headBits (n D b : ℕ) : ℕ := coefficientBits n D b + (dimension n D+1).size

noncomputable def gram (q : MvPolynomial (Fin n) ℤ) (D : ℕ) : Polynomial (Polynomial (Polynomial ℤ)) :=
  ParametricCoerciveBoxGramEliminant.polynomial (ParameterizedBoundaryGramValues.energy q)
    (ParameterizedBoundaryGramValues.degreeBound D) 0

theorem gram_map (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (e : ℤ) :
    ParametricCoerciveBoxGramEliminant.coefficientMap (Polynomial.evalRingHom e) (gram q D) =
      CoerciveBoxGramEliminant.polynomial
        ((ParameterizedBoundaryGramValues.energy q).map (Polynomial.evalRingHom e))
        (ParameterizedBoundaryGramValues.degreeBound D) 0 :=
  (ParametricCoerciveBoxGramEliminant.polynomial_map _ _ _ _).trans
    (ParametricCoerciveBoxGramEliminant.polynomial_integer _ _ _)

theorem head_eq (q : MvPolynomial (Fin n) ℤ) (D : ℕ) :
    ParameterizedBoundaryGramValues.head q D = (gram q D).trailingCoeff := rfl

attribute [local irreducible] gram ParameterizedBoundaryGramValues.energy
  CoerciveBoxGramEliminant.polynomial ParametricCoerciveBoxGramEliminant.polynomial

theorem massExponent_affine (n D b r : ℕ) :
    CoerciveBoxGramEliminant.massExponent (n+2) (ParameterizedBoundaryGramValues.degreeBound D)
      (2*r+ParameterizedBoundaryEnergyMass.energyOffset n D b) = slope n D*r+offset n D b := by
  unfold slope offset dimension CoerciveBoxGramEliminant.massExponent CoerciveRadiusBits.budgetExponent
  ring

theorem native_mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) (r : ℕ) :
    NestedMass.mass (ParametricCoerciveBoxGramEliminant.coefficientMap
      (Polynomial.evalRingHom ((2 : ℤ)^r)) (gram q D)) ≤ 2^(slope n D*r+offset n D b) := by
  rw [gram_map]
  have HD : ((ParameterizedBoundaryGramValues.energy q).map (Polynomial.evalRingHom ((2 : ℤ)^r))).totalDegree ≤
      ParameterizedBoundaryGramValues.degreeBound D :=
    (PolynomialMapDegree.degree_le _ _).trans (ParameterizedBoundaryGramValues.energy_degree q D hD)
  have H := CoerciveBoxGramEliminant.mass_le_pow _ _ _ HD
    (ParameterizedBoundaryEnergyMass.energy_mass q D b hD hq r) (0 : Fin (n+2))
  rwa [massExponent_affine] at H

private theorem coefficient_eval (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (e : ℤ) (j k : ℕ) :
    ((ParametricCoerciveBoxGramEliminant.coefficientMap (Polynomial.evalRingHom e)
      (gram q D)).coeff j).coeff k = (((gram q D).coeff j).coeff k).eval e := by
  change (((gram q D).map (Polynomial.mapRingHom (Polynomial.evalRingHom e))).coeff j).coeff k = _
  rw [Polynomial.coeff_map]
  change (((gram q D).coeff j).map (Polynomial.evalRingHom e)).coeff k = _
  rw [Polynomial.coeff_map]
  rfl

theorem coefficient_bounds (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) (j k : ℕ) :
    (((gram q D).coeff j).coeff k).natDegree ≤ slope n D ∧
      coefficientMass (((gram q D).coeff j).coeff k) ≤ 2^coefficientBits n D b := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth _ 0 (slope n D) (offset n D b)
  intro r _
  rw [←coefficient_eval q D ((2 : ℤ)^r) j k]
  exact (coeff_natAbs_le_coefficientMass _ _).trans
    ((NestedMass.coeff_le _ _).trans (native_mass q D b hD hq r))

private theorem zero_of_dyadic (f : Polynomial ℤ) (hf : ∀ r : ℕ, f.eval ((2 : ℤ)^r) = 0) : f = 0 := by
  have HD : f.natDegree ≤ 0 := IntegerPolynomialDyadic.natDegree_le f 0 0 0 (by
    intro r _
    rw [hf r]
    norm_num)
  have HC := Polynomial.eq_C_of_natDegree_le_zero HD
  have H := hf 0
  rw [HC,Polynomial.eval_C] at H
  rw [HC,H,Polynomial.C_0]

private theorem mapped_inner_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (e : ℤ) (j : ℕ) :
    ((ParametricCoerciveBoxGramEliminant.coefficientMap (Polynomial.evalRingHom e)
      (gram q D)).coeff j).natDegree ≤ dimension n D := by
  rw [gram_map]
  have HD : ((ParameterizedBoundaryGramValues.energy q).map (Polynomial.evalRingHom e)).totalDegree ≤
      ParameterizedBoundaryGramValues.degreeBound D :=
    (PolynomialMapDegree.degree_le _ _).trans (ParameterizedBoundaryGramValues.energy_degree q D hD)
  simpa only [dimension] using CoerciveBoxGramEliminant.inner_degree _ _ HD (0 : Fin (n+2)) j

theorem inner_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) (j : ℕ) :
    ((gram q D).coeff j).natDegree ≤ dimension n D := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply zero_of_dyadic
  intro r
  rw [←coefficient_eval q D ((2 : ℤ)^r) j k]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (mapped_inner_degree q D hD ((2 : ℤ)^r) j).trans_lt hk

theorem head_degree (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) :
    (ParameterizedBoundaryGramValues.head q D).natDegree ≤ dimension n D := by
  rw [head_eq,Polynomial.trailingCoeff]
  exact inner_degree q D hD _

theorem head_mass (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) :
    NestedMass.mass (ParameterizedBoundaryGramValues.head q D) ≤ 2^headBits n D b := by
  apply NestedMass.le_pow _ (dimension n D) (coefficientBits n D b) (head_degree q D hD)
  intro k
  rw [head_eq,Polynomial.trailingCoeff]
  exact (coefficient_bounds q D b hD hq _ k).2

end LeanCanny.Geometry.ParameterizedBoundaryGramMass
