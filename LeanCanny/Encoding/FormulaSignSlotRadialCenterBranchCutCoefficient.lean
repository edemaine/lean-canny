/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutFamily
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # Actual branch-cut radius coefficients as integer center polynomials -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficient
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotRadialCenterPrincipalFamily
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (k r : ℕ) : MvPolynomial (Fin (d (pairFst (original c)))) ℤ :=
  MvTwoParameterCoefficient.one (FormulaSignSlotRadialCenterBranchCutFamily.polynomial c k) r

theorem polynomial_eq (c : List Bool) (k r : ℕ) : polynomial c k r =
    (FormulaSignSlotRadialCenterBranchCut.polynomial (original c) (tau c) (degree c) k).coeff r := by
  rw [polynomial, FormulaSignSlotRadialCenterBranchCutFamily.polynomial_map]
  unfold MvTwoParameterCoefficient.one TriplePolynomialParameterFlatten.one
  change ((MvPolynomial.finSuccEquiv ℤ _)
    ((MvPolynomial.finSuccEquiv ℤ _).symm
      (FormulaSignSlotRadialCenterBranchCut.polynomial (original c) (tau c)
        (FormulaSignSlotRadialCenterPrincipalFamily.degree c) k))).coeff r = _
  rw [AlgEquiv.apply_symm_apply]

theorem coefficient (c : List Bool) (k r : ℕ) (v : Fin (d (pairFst (original c))) →₀ ℕ) :
    (polynomial c k r).coeff v = (FormulaSignSlotRadialCenterBranchCutFamily.polynomial c k).coeff (v.cons r) :=
  MvPolynomial.finSuccEquiv_coeff_coeff _ _ _

theorem degree (c : List Bool) (k r : ℕ) :
    (polynomial c k r).totalDegree ≤ FormulaSignSlotRadialCenterBranchCutFamily.degreeBound c :=
  (MvTwoParameterCoefficient.one_degree _ _).trans (FormulaSignSlotRadialCenterBranchCutFamily.polynomial_degree c k)
theorem mass (c : List Bool) (k r : ℕ) :
    MvMass.mass (polynomial c k r) ≤ 2 ^ FormulaSignSlotRadialCenterBranchCutFamily.massBound c :=
  (MvTwoParameterCoefficient.one_mass _ _).trans (FormulaSignSlotRadialCenterBranchCutFamily.polynomial_mass c k)

theorem specialization (c : List Bool) (a : Fin (d (pairFst (original c))) → ℝ) (k r : ℕ)
    (h : FormulaSignSlotRadialCenterSquarefreeSelection.Guards (original c) a (tau c)
      (FormulaSignSlotRadialCenterPrincipalFamily.degree c) k) :
    (LeanCanny.Geometry.RealParameterRootBranches.cut
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (original c) a)).coeff r =
        (polynomial c k r).eval₂ (Int.castRingHom ℝ) a := by
  rw [← FormulaSignSlotRadialCenterBranchCut.specialization (original c) a (tau c) _ k h, polynomial_eq]
  unfold FormulaSignSlotRadialFormalCenter.radiusMap
  rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficient
