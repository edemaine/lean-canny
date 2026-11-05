/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.TriplePolynomialParameterFlatten
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantNormalized
/-! # The actual homogeneous system with every formal parameter in one block

Parameter variables are epsilon, target, radius, then center. Flattening is a
ring homomorphism and commutes with the actual normalized universal value.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterRows
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MacaulayUniversal.polynomialValue

noncomputable local instance radialParameterCenterRing (a : ℕ) : CommRing (MvPolynomial (Fin a) ℤ) := inferInstance
noncomputable local instance radialParameterRadiusRing (a : ℕ) : CommRing (Polynomial (MvPolynomial (Fin a) ℤ)) := inferInstance
noncomputable local instance radialParameterTargetRing (a : ℕ) : CommRing (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ))) := inferInstance
noncomputable local instance radialParameterPerturbationRing (a : ℕ) : CommRing (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) := inferInstance

noncomputable def row (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (j : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1)) :=
  (FormulaSignSlotRadialEliminantRows.system c i j).map TriplePolynomialParameterFlatten.flatten

noncomputable def eliminant (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :=
  TriplePolynomialParameterFlatten.flatten (FormulaSignSlotRadialFormalEliminant.eliminant c i)

theorem coefficient (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (j : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    ((row c i j).coeff e).coeff (TriplePolynomialParameterFlatten.exponent s t r v) =
      (((((FormulaSignSlotRadialEliminantRows.system c i j).coeff e).coeff s).coeff t).coeff r).coeff v := by
  rw [row, coeff_map, TriplePolynomialParameterFlatten.coefficient]

theorem homogeneous (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (j : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1)) :
    (row c i j).IsHomogeneous (CoerciveCriticalHomogenization.finDegree (degreeBudget c) j) :=
  (FormulaSignSlotRadialEliminantRows.spatial_homogeneous c i j).map _

theorem polynomialValue (c : List Bool) (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) :
    MacaulayUniversal.polynomialValue (CoerciveCriticalHomogenization.finDegree (degreeBudget c))
      (FormulaSignSlotRadialEliminantNormalized.width c) (CoerciveCoordinateEliminant.degree_lt _ _)
      (CoerciveCoordinateEliminant.level_lt _ _) (row c i) = eliminant c i := by
  have H := MacaulayUniversal.polynomialValue_map
    (n := FormulaSignSlotRadialFormalInput.spatial c) TriplePolynomialParameterFlatten.flatten
    (CoerciveCriticalHomogenization.finDegree (degreeBudget c))
    (FormulaSignSlotRadialEliminantNormalized.width c)
    (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
    (FormulaSignSlotRadialEliminantRows.system c i)
  have HE : eliminant c i = TriplePolynomialParameterFlatten.flatten
      (MacaulayUniversal.polynomialValue
        (CoerciveCriticalHomogenization.finDegree (degreeBudget c))
        (FormulaSignSlotRadialEliminantNormalized.width c)
        (CoerciveCoordinateEliminant.degree_lt _ _) (CoerciveCoordinateEliminant.level_lt _ _)
        (FormulaSignSlotRadialEliminantRows.system c i)) := rfl
  rw [HE, show row c i = (fun j =>
    (FormulaSignSlotRadialEliminantRows.system c i j).map TriplePolynomialParameterFlatten.flatten) from rfl]
  exact H.symm

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterRows
