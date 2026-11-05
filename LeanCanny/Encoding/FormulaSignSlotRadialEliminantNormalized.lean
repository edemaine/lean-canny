/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayPaddedPolynomialValue
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRows
public import LeanCanny.Connectivity.FormulaSignSlotRadialFormalEliminant
/-! # The actual formal radial eliminant as a monic padded quotient

All center, radius, target and perturbation variables remain in the coefficient
ring. No nonvanishing hypothesis on a specialized extraneous determinant is
needed. This identity is the normalization contract for the native reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantNormalized
open LeanCanny.Algebra LeanCanny.Connectivity
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable local instance radialNormalizedCenterRing (a : ℕ) : CommRing (MvPolynomial (Fin a) ℤ) := inferInstance
noncomputable local instance radialNormalizedRadiusRing (a : ℕ) : CommRing (Polynomial (MvPolynomial (Fin a) ℤ)) := inferInstance
noncomputable local instance radialNormalizedTargetRing (a : ℕ) : CommRing (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ))) := inferInstance
noncomputable local instance radialNormalizedPerturbationRing (a : ℕ) : CommRing (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) := inferInstance
noncomputable local instance radialNormalizedCenterDomain (a : ℕ) : IsDomain (MvPolynomial (Fin a) ℤ) := inferInstance
noncomputable local instance radialNormalizedRadiusDomain (a : ℕ) : IsDomain (Polynomial (MvPolynomial (Fin a) ℤ)) := inferInstance
noncomputable local instance radialNormalizedTargetDomain (a : ℕ) : IsDomain (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ))) := inferInstance
noncomputable local instance radialNormalizedPerturbationDomain (a : ℕ) : IsDomain (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) := inferInstance

noncomputable def width (c : List Bool) :=
  CoerciveCoordinateEliminant.width (FormulaSignSlotRadialFormalInput.spatial c) (degreeBudget c)

noncomputable def quotient (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :=
  MacaulayPaddedPolynomialValue.quotient (FormulaSignSlotRadialEliminantRows.system c i)
    (CoerciveCriticalHomogenization.finDegree (degreeBudget c)) (width c)

theorem quotient_eq (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    quotient c i = Macaulay.characteristicQuotient (FormulaSignSlotRadialEliminantRows.system c i)
      (CoerciveCriticalHomogenization.finDegree (degreeBudget c)) (width c) :=
  MacaulayPaddedPolynomialValue.quotient_eq _ _ _
    (FormulaSignSlotRadialEliminantRows.spatial_homogeneous c i)
    (CoerciveCriticalHomogenization.finDegree_pos _) (CoerciveCoordinateEliminant.level_lt _ _)

theorem coefficient_zero (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    (quotient c i).coeff 0 = FormulaSignSlotRadialFormalEliminant.eliminant c i := by
  exact (MacaulayPaddedPolynomialValue.value_eq_coefficient_zero _ _
    (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
    (FormulaSignSlotRadialEliminantRows.system c i)
    (FormulaSignSlotRadialEliminantRows.spatial_homogeneous c i)
    (CoerciveCriticalHomogenization.finDegree_pos _)).symm

theorem divisor_monic (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    (MacaulayPaddedPolynomialValue.divisor (FormulaSignSlotRadialEliminantRows.system c i)
      (CoerciveCriticalHomogenization.finDegree (degreeBudget c)) (width c)).Monic :=
  Matrix.charpoly_monic _

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantNormalized
