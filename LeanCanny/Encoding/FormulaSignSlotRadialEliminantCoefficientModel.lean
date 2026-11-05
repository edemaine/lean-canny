/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantRows
/-! # One dense original coefficient and sparse arithmetic give an actual system row -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientModel
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def extract (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    FormulaSignSlotRadialFormalCenter.Radius c →+ ℤ :=
  (MvPolynomial.lcoeff ℤ v).toAddMonoidHom.comp (Polynomial.lcoeff _ r).toAddMonoidHom

private theorem extract_integer (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ) (z : ℤ) :
    extract c r v (Polynomial.C (MvPolynomial.C z)) = if r = 0 ∧ v = 0 then z else 0 := by
  change ((Polynomial.C (MvPolynomial.C z)).coeff r).coeff v = _
  rw [Polynomial.coeff_C]
  by_cases hr : r = 0
  · subst r
    rw [ite_eq_left rfl, MvPolynomial.coeff_C]
    simp only [true_and, eq_comm]
  · rw [ite_eq_right hr]
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hr, false_and, ite_false]

private theorem extract_if (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ)
    (P : Prop) [Decidable P] (a b : FormulaSignSlotRadialFormalCenter.Radius c) :
    extract c r v (if P then a else b) = if P then extract c r v a else extract c r v b := by
  split_ifs <;> rfl

noncomputable def dense (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ) (r : ℕ) (v : Fin (d c) →₀ ℕ) : ℤ :=
  (pderiv (FormulaSignSlotRadialFormalInput.spatialIndex c j)
    ((FormulaSignSlotRadialFormalInput.polynomial c) ^ 2)).coeff
      (FormulaSignSlotRadialEliminantSource.exponent c e r v)

noncomputable def kernel (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) (z : ℤ) : ℤ :=
  (if Finsupp.weight (WeightedHomogenization.weights (fun _ : Fin (FormulaSignSlotRadialFormalInput.spatial c) => 1)) e = 2 * degreeBudget c + 1
    then (if s = 0 ∧ t = 0 then z else 0) -
      (if j = marginIndex c then (if e.some = 0 then (if s = 1 ∧ t = 0 then
        (if r = 0 ∧ v = 0 then 1 else 0) else 0) else 0) else 0)
    else 0) +
  (if Finsupp.single (some j) (2 * degreeBudget c + 1) = e
    then (if s = 2 ∧ t = 0 then (if r = 0 ∧ v = 0 then ((2 * degreeBudget c + 2 : ℕ) : ℤ) else 0) else 0)
    else 0)

noncomputable def gradient (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) : ℤ :=
  kernel c j e s t r v (dense c j e.some r v)

theorem gradient_eq (c : List Bool) (coordinate j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (FormulaSignSlotRadialEliminantRows.polynomial c coordinate (CoerciveCriticalHomogenization.layout (some j))).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (e.mapDomain CoerciveCriticalHomogenization.layout) s t r v) =
        gradient c j e s t r v := by
  rw [FormulaSignSlotRadialEliminantRows.coefficient]
  change extract c r v ((((rename CoerciveCriticalHomogenization.layout
    (TiltedCoerciveCriticalFibers.nativeSystem
      ((FormulaSignSlotRadialFormalCenter.polynomial c).map ParametricTiltedCoerciveEliminant.constants)
      (degreeBudget c) (marginIndex c) Polynomial.X (Polynomial.C Polynomial.X) coordinate (some j))).coeff
      (e.mapDomain CoerciveCriticalHomogenization.layout)).coeff s).coeff t) = _
  rw [coeff_rename_mapDomain _ CoerciveCriticalHomogenization.layout.injective]
  change extract c r v ((((TiltedCoerciveCriticalFibers.nativeSystem
      ((FormulaSignSlotRadialFormalCenter.polynomial c).map ParametricTiltedCoerciveEliminant.constants)
      (degreeBudget c) (marginIndex c) Polynomial.X (Polynomial.C Polynomial.X) (marginIndex c) (some j)).coeff e).coeff s).coeff t) = _
  rw [ParametricTiltedCoerciveCoefficient.gradient]
  have HD : extract c r v ((pderiv j ((FormulaSignSlotRadialFormalCenter.polynomial c) ^ 2)).coeff e.some) =
      dense c j e.some r v := (FormulaSignSlotRadialEliminantSource.source_derivative_coefficient c j e.some r v).symm
  have HOne : (1 : FormulaSignSlotRadialFormalCenter.Radius c) = Polynomial.C (MvPolynomial.C (1 : ℤ)) := by simp
  have HNat : (((2 * degreeBudget c + 2 : ℕ) : FormulaSignSlotRadialFormalCenter.Radius c)) =
      Polynomial.C (MvPolynomial.C ((2 * degreeBudget c + 2 : ℕ) : ℤ)) := by simp only [map_natCast]
  simp only [map_add, map_sub, extract_if, map_zero, HOne, HNat, extract_integer]
  exact congrArg (kernel c j e s t r v) HD

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientModel
