/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHead
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterTrailingSelection
/-! # The actual leading and margin radius heads after same-center selection -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadEvaluation
open LeanCanny.Algebra LeanCanny.Connectivity Polynomial MvPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

noncomputable def radiusPolynomial (c : List Bool) (tau eta : ℕ) :=
  MvPolynomial.finSuccEquiv ℤ (d (pairFst c)) (FormulaSignSlotRadialRadiusHead.polynomial c tau eta)

theorem coefficient (c : List Bool) (tau eta r : ℕ) : (radiusPolynomial c tau eta).coeff r=
    FormulaSignSlotRadialCenterCoefficient.polynomial c tau eta r := by
  ext v
  rw [radiusPolynomial,MvPolynomial.finSuccEquiv_coeff_coeff,FormulaSignSlotRadialRadiusHead.coefficient]

theorem specialization (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau eta : ℕ) :
    (radiusPolynomial c tau eta).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)=
      ((FormulaSignSlotRadialParameterEliminant.eliminant (pairFst c) a
        (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff tau).coeff eta := by
  ext r
  rw [Polynomial.coeff_map,coefficient]
  exact (FormulaSignSlotRadialCenterCoefficient.specialization c a tau eta r).symm

theorem leading (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D : ℕ)
    (H : FormulaSignSlotRadialCenterSelection.Guards c a tau D) :
    (radiusPolynomial c tau D).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)=
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff := by
  rw [specialization,(FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp H |>.1]
  change (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).coeff D=_
  rw [Polynomial.leadingCoeff,FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree c a tau D H]

theorem trailing (c : List Bool) (a : Fin (d (pairFst c)) → ℝ) (tau D ell : ℕ)
    (H : FormulaSignSlotRadialCenterTrailingSelection.Guards c a tau D ell) :
    (radiusPolynomial c tau ell).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) a)=
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff := by
  have HH := (FormulaSignSlotRadialCenterTrailingSelection.guards_iff c a tau D ell).mp H
  rw [specialization,(FormulaSignSlotRadialCenterSelection.guards_iff c a tau D).mp HH.1 |>.1]
  change (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).coeff ell=_
  rw [HH.2]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadEvaluation
