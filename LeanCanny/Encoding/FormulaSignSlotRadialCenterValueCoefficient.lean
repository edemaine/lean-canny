/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
/-! # Literal radius coefficients of the actual formal value certificate -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoefficient
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial
open FormulaSignSlotCenteredRadialGraph
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (c : List Bool) (j r : ℕ) :
    MvPolynomial (Fin (d (FormulaSignSlotRadialCenterValueLayout.original c))) ℤ :=
  ((FormulaSignSlotRadialCenterValuePacking.source c).coeff j).coeff r

theorem coefficient (c : List Bool) (j r : ℕ)
    (v : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) →₀ ℕ) :
    (polynomial c j r).coeff v = (TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValuePacking.source c).coeff j)).coeff (v.cons r) :=
  (TriplePolynomialParameterFlatten.one_coefficient _ r v).symm

theorem polynomial_eq (c : List Bool) (j r : ℕ) : polynomial c j r =
    MvTwoParameterCoefficient.one (TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValuePacking.source c).coeff j)) r := by
  unfold MvTwoParameterCoefficient.one TriplePolynomialParameterFlatten.one
  change _ = ((MvPolynomial.finSuccEquiv ℤ _) ((MvPolynomial.finSuccEquiv ℤ _).symm _)).coeff r
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem degree (c : List Bool) (j r : ℕ) : (polynomial c j r).totalDegree ≤
    FormulaSignSlotRadialCenterValuePacking.degree c := by
  rw [polynomial_eq]
  exact (MvTwoParameterCoefficient.one_degree _ _).trans
    (FormulaSignSlotRadialCenterValuePacking.source_degree c j)

theorem specialization (c : List Bool)
    (a : Fin (d (FormulaSignSlotRadialCenterValueLayout.original c)) → ℝ) (j r : ℕ)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original c) a
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau c i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree c i.val)) :
    (((FormulaSignSlotRadialValueCertificate.polynomial
      (FormulaSignSlotRadialCenterValueLayout.original c) a).coeff j).coeff r) =
        (polynomial c j r).eval₂ (Int.castRingHom ℝ) a := by
  rw [← FormulaSignSlotRadialCenterValueFamily.specialization _ a _ _ h]
  simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoefficient
