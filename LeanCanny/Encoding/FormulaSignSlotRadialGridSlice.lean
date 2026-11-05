/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
public import LeanCanny.Algebra.MvTwoParameterCoefficient
/-! # The literal radial grid slice retains target, radius, and center

Only the perturbation exponent is selected. This is an actual coefficient
of the normalized formal eliminant, before any real specialization.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialGridSlice
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

noncomputable def polynomial (c : List Bool) (tau : ℕ) : MvPolynomial (Fin (d (pairFst c)+2)) ℤ :=
  TriplePolynomialParameterFlatten.two ((FormulaSignSlotRadialFormalEliminant.eliminant
    (pairFst c) (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau)

private theorem head {a : ℕ} (p : Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) (s : ℕ) :
    MvTwoParameterCoefficient.one (TriplePolynomialParameterFlatten.flatten p) s =
      TriplePolynomialParameterFlatten.two (p.coeff s) := by
  change ((MvPolynomial.finSuccEquiv ℤ (a+2)) ((MvPolynomial.finSuccEquiv ℤ (a+2)).symm
    (p.map TriplePolynomialParameterFlatten.two))).coeff s = _
  rw [AlgEquiv.apply_symm_apply, Polynomial.coeff_map]

private theorem two_coefficient {a : ℕ} (p : Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))
    (t r : ℕ) (v : Fin a →₀ ℕ) :
    (TriplePolynomialParameterFlatten.two p).coeff ((v.cons r).cons t) = ((p.coeff t).coeff r).coeff v := by
  change (TriplePolynomialParameterFlatten.one (p.map TriplePolynomialParameterFlatten.one)).coeff _ = _
  rw [TriplePolynomialParameterFlatten.one_coefficient, Polynomial.coeff_map,
    TriplePolynomialParameterFlatten.one_coefficient]

theorem as_coefficient (c : List Bool) (tau : ℕ) : polynomial c tau =
    MvTwoParameterCoefficient.one (FormulaSignSlotRadialEliminantParameterRows.eliminant
      (pairFst c) (FormulaSignSlotRadialEliminantInput.coordinate c)) tau :=
  (head _ tau).symm

theorem coefficient (c : List Bool) (tau t r : ℕ) (v : Fin (d (pairFst c)) →₀ ℕ) :
    (polynomial c tau).coeff ((v.cons r).cons t) =
      (FormulaSignSlotRadialCenterCoefficient.polynomial c tau t r).coeff v := two_coefficient _ t r v

theorem degree (c : List Bool) (tau : ℕ) : (polynomial c tau).totalDegree ≤
    FormulaSignSlotRadialEliminantPacked.resultDegree c := by
  rw [as_coefficient]
  exact (MvTwoParameterCoefficient.one_degree _ _).trans (FormulaSignSlotRadialEliminantPacked.result_degree c)

theorem mass (c : List Bool) (tau : ℕ) : MvMass.mass (polynomial c tau) ≤
    2^FormulaSignSlotRadialEliminantFormalMass.budget c := by
  rw [as_coefficient]
  exact (MvTwoParameterCoefficient.one_mass _ _).trans (FormulaSignSlotRadialEliminantFormalMass.parameter_mass c)

theorem fit (c : List Bool) (tau : ℕ) : (polynomial c tau).totalDegree <
    2^FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c :=
  (degree c tau).trans_lt (FormulaSignSlotRadialEliminantPacked.result_fit c)

end LeanCanny.Encoding.FormulaSignSlotRadialGridSlice
