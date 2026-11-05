/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalMass
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # Concrete integer center polynomials for the radial principal zero tests -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalCoefficient
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial PrincipalSubresultant
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotRadialCenterPrincipalFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (j r : ℕ) : MvPolynomial (Fin (d (pairFst (original c)))) ℤ :=
  MvTwoParameterCoefficient.one (principal c j) r

noncomputable def radiusPolynomial (c : List Bool) (j : ℕ) :=
  signedPsc (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial (original c) (tau c) (degree c))
    (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial (original c) (tau c) (degree c)).derivative
      (degree c) (degree c - 1) j

theorem polynomial_eq (c : List Bool) (j r : ℕ) : polynomial c j r = (radiusPolynomial c j).coeff r := by
  rw [polynomial, principal_map]
  unfold MvTwoParameterCoefficient.one TriplePolynomialParameterFlatten.one
  change ((MvPolynomial.finSuccEquiv ℤ _)
    ((MvPolynomial.finSuccEquiv ℤ _).symm (radiusPolynomial c j))).coeff r = _
  rw [AlgEquiv.apply_symm_apply]

theorem coefficient (c : List Bool) (j r : ℕ) (v : Fin (d (pairFst (original c))) →₀ ℕ) :
    (polynomial c j r).coeff v = (principal c j).coeff (v.cons r) :=
  MvPolynomial.finSuccEquiv_coeff_coeff _ _ _

theorem degree (c : List Bool) (j r : ℕ) : (polynomial c j r).totalDegree ≤ degreeBound c :=
  (MvTwoParameterCoefficient.one_degree _ _).trans (principal_degree c j)

theorem mass (c : List Bool) (j r : ℕ) :
    MvMass.mass (polynomial c j r) ≤ 2 ^ FormulaSignSlotRadialCenterPrincipalMass.budget c :=
  (MvTwoParameterCoefficient.one_mass _ _).trans (FormulaSignSlotRadialCenterPrincipalMass.mass c j)

theorem zero_of_large_radius (c : List Bool) (j r : ℕ) (hr : degreeBound c < r) : polynomial c j r = 0 :=
  MvTwoParameterCoefficient.one_eq_zero _ _ ((principal_degree c j).trans_lt hr)

noncomputable def specialized (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j : ℕ) :=
  (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst (original c)) a) (radiusPolynomial c j)

theorem specialization (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j r : ℕ) :
    (specialized c a j).coeff r = (polynomial c j r).eval₂ (Int.castRingHom ℝ) a := by
  rw [polynomial_eq]
  unfold specialized FormulaSignSlotRadialFormalCenter.radiusMap
  rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

theorem radius_degree (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j : ℕ) :
    (specialized c a j).natDegree ≤ degreeBound c := by
  have HE : radiusPolynomial c j = (MvPolynomial.finSuccEquiv ℤ _) (principal c j) := by
    rw [principal_map]
    unfold TriplePolynomialParameterFlatten.one
    exact (AlgEquiv.apply_symm_apply _ _).symm
  apply Polynomial.natDegree_map_le.trans
  rw [HE, MvPolynomial.natDegree_finSuccEquiv]
  exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans (principal_degree c j)

theorem zero_iff (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j : ℕ) :
    (∀ r < degreeBound c + 1, (polynomial c j r).eval₂ (Int.castRingHom ℝ) a = 0) ↔ specialized c a j = 0 := by
  constructor
  · intro H
    apply Polynomial.ext
    intro r
    rw [Polynomial.coeff_zero]
    by_cases hr : r < degreeBound c + 1
    · exact (specialization c a j r).trans (H r hr)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((radius_degree c a j).trans_lt (by omega))
  · intro H r _
    rw [← specialization, H, Polynomial.coeff_zero]

theorem unsigned_zero_iff (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (j : ℕ)
    (hj : j < FormulaSignSlotRadialCenterPrincipalFamily.degree c) :
    specialized c a j = 0 ↔
      (FormulaSignSlotRadialFormalCenter.radiusMap (pairFst (original c)) a)
        (FormulaSignSlotRadialCenterSquarefreeSelection.principal (original c) (tau c)
          (FormulaSignSlotRadialCenterPrincipalFamily.degree c) j) = 0 := by
  have HJ : j ≤ min (FormulaSignSlotRadialCenterPrincipalFamily.degree c)
      (FormulaSignSlotRadialCenterPrincipalFamily.degree c - 1) := by omega
  rw [specialized, radiusPolynomial, signedPsc_of_le _ _ HJ, map_mul, map_pow, map_neg, map_one]
  change (-1 : Polynomial ℝ) ^ _ * _ = 0 ↔ _
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalCoefficient
