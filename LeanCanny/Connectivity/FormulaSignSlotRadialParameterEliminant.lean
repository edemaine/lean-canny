/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialParameterPolynomial
/-! # Actual radius-coordinate equations from the tilted perturbation limit

The parameter coefficient ring retains the fixed center. The perturbation
variable is removed only after constructing the nonzero universal eliminant.
Outside finitely many actual coefficient roots, specialization commutes with
that lowest perturbation coefficient and gives the proved finite slice grid.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialParameterEliminant
open ETR Set Polynomial MvPolynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial

noncomputable def eliminant (c : List Bool) (a : Fin (d c) → ℝ) (i : Fin (N c+d c+1)) :
    Polynomial (Polynomial (Polynomial ℝ)) :=
  ParametricTiltedCoerciveEliminant.polynomial (FormulaSignSlotRadialParameterPolynomial.polynomial c a)
    (degreeBudget c) (marginIndex c) i

theorem eliminant_specialization (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (i : Fin (N c+d c+1)) :
    ParametricTiltedCoerciveEliminant.coefficientMap (Polynomial.evalRingHom r) (eliminant c a i)=
      ParametricTiltedCoerciveEliminant.polynomial
        (FormulaSignSlotCenteredRadialLimits.polynomial c a r) (degreeBudget c) (marginIndex c) i := by
  unfold eliminant
  rw [ParametricTiltedCoerciveEliminant.polynomial_map,FormulaSignSlotRadialParameterPolynomial.specialization]

theorem specialized_ne_zero (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ) (i : Fin (N c+d c+1)) :
    ParametricTiltedCoerciveEliminant.coefficientMap (Polynomial.evalRingHom r) (eliminant c a i)≠0 := by
  rw [eliminant_specialization]
  exact ParametricTiltedCoerciveEliminant.ne_zero Complex.ofRealHom _ _ (polynomial_degree c a r) (marginIndex c) i

theorem eliminant_ne_zero (c : List Bool) (a : Fin (d c) → ℝ) (i : Fin (N c+d c+1)) : eliminant c a i≠0 := by
  intro H
  exact specialized_ne_zero c a 0 i (by rw [H,map_zero])

noncomputable def coordinate (c : List Bool) (a : Fin (d c) → ℝ) (i : Fin (N c+d c+1)) :
    Polynomial (Polynomial ℝ) := (eliminant c a i).trailingCoeff

theorem coordinate_ne_zero (c : List Bool) (a : Fin (d c) → ℝ) (i : Fin (N c+d c+1)) : coordinate c a i≠0 :=
  Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (eliminant_ne_zero c a i)

noncomputable def bad (c : List Bool) (a : Fin (d c) → ℝ) : Set ℝ :=
  {r | ∃ i, (coordinate c a i).leadingCoeff.eval r=0}

theorem finite_bad (c : List Bool) (a : Fin (d c) → ℝ) : (bad c a).Finite := by
  have H := Set.finite_iUnion (fun i : Fin (N c+d c+1) =>
    Polynomial.finite_setOfPred_isRoot (Polynomial.leadingCoeff_ne_zero.mpr (coordinate_ne_zero c a i)))
  exact H.subset (fun r ⟨i,hi⟩ => Set.mem_iUnion.mpr ⟨i,hi⟩)

theorem mapped_coordinate_ne_zero (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (hr : r∉bad c a) (i : Fin (N c+d c+1)) : (coordinate c a i).map (Polynomial.evalRingHom r)≠0 := by
  have HI : (coordinate c a i).leadingCoeff.eval r≠0 := fun H => hr ⟨i,H⟩
  intro HZ
  have HC := congrArg (fun p : Polynomial ℝ => p.coeff (coordinate c a i).natDegree) HZ
  apply HI
  simpa only [Polynomial.coeff_map,Polynomial.coeff_zero,Polynomial.leadingCoeff,Polynomial.coe_evalRingHom] using HC

theorem coordinate_specialization (c : List Bool) (a : Fin (d c) → ℝ) (r : ℝ)
    (hr : r∉bad c a) (i : Fin (N c+d c+1)) :
    (coordinate c a i).map (Polynomial.evalRingHom r)=
      TiltedCoerciveComponentEliminants.coordinate (FormulaSignSlotCenteredRadialLimits.polynomial c a r)
        (degreeBudget c) (marginIndex c) i := by
  have H := trailingCoeff_map_of_survives (Polynomial.mapRingHom (Polynomial.evalRingHom r)) (eliminant c a i)
    (mapped_coordinate_ne_zero c a r hr i)
  change (ParametricTiltedCoerciveEliminant.coefficientMap (Polynomial.evalRingHom r) (eliminant c a i)).trailingCoeff=
    (coordinate c a i).map (Polynomial.evalRingHom r) at H
  rw [eliminant_specialization] at H
  exact H.symm

end LeanCanny.Connectivity.FormulaSignSlotRadialParameterEliminant
