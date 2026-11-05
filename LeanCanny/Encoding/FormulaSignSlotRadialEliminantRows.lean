/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantSource
public import LeanCanny.Algebra.ParametricTiltedCoerciveCoefficient
/-! # Exact full integer rows of the actual formal radial eliminant system

The integer layout is radius, target, perturbation, homogeneous spatial block,
then center. This is the literal system input, not an expanded resultant.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantRows
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable local instance radialEliminantCenterCommRing (a : ℕ) : CommRing (MvPolynomial (Fin a) ℤ) := inferInstance
noncomputable local instance radialEliminantRadiusCommRing (a : ℕ) : CommRing (Polynomial (MvPolynomial (Fin a) ℤ)) := inferInstance
noncomputable local instance radialEliminantTargetCommRing (a : ℕ) : CommRing (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ))) := inferInstance
noncomputable local instance radialEliminantPerturbationCommRing (a : ℕ) : CommRing (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) := inferInstance


noncomputable def dimension (c : List Bool) := FormulaSignSlotRadialFormalInput.spatial c + 4 + d c

noncomputable def system (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1)) :=
  ParametricTiltedCoerciveEliminant.system (FormulaSignSlotRadialFormalCenter.polynomial c)
    (degreeBudget c) (marginIndex c) coordinate row

noncomputable def flatten {n a : ℕ} :
    MvPolynomial (Fin (n + 1)) (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) →+*
      MvPolynomial (Fin (n + 4 + a)) ℤ :=
  (rename finSumFinEquiv).toRingHom.comp (NestedPolynomial.flatten.comp
    (IntegerParameterFlatten.flatten.comp (IntegerParameterFlatten.flatten.comp IntegerParameterFlatten.flatten)))

noncomputable def polynomial (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1)) := flatten (system c coordinate row)

noncomputable def exponent {n a : ℕ} (e : Fin (n + 1) →₀ ℕ) (s t r : ℕ)
    (v : Fin a →₀ ℕ) : Fin (n + 4 + a) →₀ ℕ :=
  (NestedPolynomial.joinExponent (IntegerParameterFlatten.joinExponent r
    (IntegerParameterFlatten.joinExponent t (IntegerParameterFlatten.joinExponent s e))) v).mapDomain finSumFinEquiv

theorem flatten_coefficient {n a : ℕ}
    (p : MvPolynomial (Fin (n + 1)) (Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))))
    (e : Fin (n + 1) →₀ ℕ) (s t r : ℕ) (v : Fin a →₀ ℕ) :
    (flatten p).coeff (exponent e s t r v) = (((((p.coeff e).coeff s).coeff t).coeff r).coeff v) := by
  change (rename finSumFinEquiv (NestedPolynomial.flatten
    (IntegerParameterFlatten.flatten (IntegerParameterFlatten.flatten (IntegerParameterFlatten.flatten p))))).coeff
      ((NestedPolynomial.joinExponent (IntegerParameterFlatten.joinExponent r
        (IntegerParameterFlatten.joinExponent t (IntegerParameterFlatten.joinExponent s e))) v).mapDomain finSumFinEquiv) = _
  rw [coeff_rename_mapDomain _ finSumFinEquiv.injective, NestedPolynomial.coefficient]
  have HT {k : ℕ} (u : ℕ) (f : Fin k →₀ ℕ) :
      IntegerParameterFlatten.tailExponent (IntegerParameterFlatten.joinExponent u f) = f := by
    ext i
    exact IntegerParameterFlatten.joinExponent_succ u f i
  simp only [IntegerParameterFlatten.coeff_flatten, HT, IntegerParameterFlatten.joinExponent_zero]

theorem coefficient (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1) →₀ ℕ) (s t r : ℕ)
    (v : Fin (d c) →₀ ℕ) :
    (polynomial c coordinate row).coeff (exponent e s t r v) =
      (((((system c coordinate row).coeff e).coeff s).coeff t).coeff r).coeff v :=
  flatten_coefficient _ e s t r v

theorem spatial_homogeneous (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (row : Fin (FormulaSignSlotRadialFormalInput.spatial c + 1)) :
    (system c coordinate row).IsHomogeneous (CoerciveCriticalHomogenization.finDegree (degreeBudget c) row) :=
  ParametricTiltedCoerciveEliminant.homogeneous _ _ _ _ _

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantRows
