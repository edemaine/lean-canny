/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoordinateCoefficient
/-! # Both native row readers return literal full integer system coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial MatrixPower
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem gradientValue_correct (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (j : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) (q : List Bool)
    (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) :
    gradientValue read W target head epsilon targetParameter modulus j q =
      residueBits (((FormulaSignSlotRadialEliminantRows.polynomial (read q) coordinate
        (CoerciveCriticalHomogenization.layout (some (j q)))).coeff
          (FormulaSignSlotRadialEliminantRows.exponent
            ((homogeneousExponent read W target head q).mapDomain CoerciveCriticalHomogenization.layout)
            (Nat.fromBitsLE (epsilon q)) (Nat.fromBitsLE (targetParameter q))
            (FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q))
            (FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q))) : ℤ) :
              ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus q) + 1)))
    (FormulaSignSlotRadialEliminantCoefficientModel.gradient_eq (read q) coordinate (j q)
      (homogeneousExponent read W target head q) _ _ _ _).symm

private theorem extract_integer (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    FormulaSignSlotRadialEliminantCoefficientModel.extract c r v (1 : FormulaSignSlotRadialFormalCenter.Radius c) =
      if r = 0 ∧ v = 0 then (1 : ℤ) else 0 := by
  change (((1 : Polynomial (MvPolynomial (Fin (d c)) ℤ)).coeff r).coeff v) = _
  by_cases hr : r = 0
  · subst r
    simp only [Polynomial.coeff_one_zero, MvPolynomial.coeff_one, true_and, eq_comm]
  · rw [Polynomial.coeff_one]
    simp only [hr, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, false_and]

private theorem extract_if (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ)
    (P : Prop) [Decidable P] (a b : FormulaSignSlotRadialFormalCenter.Radius c) :
    FormulaSignSlotRadialEliminantCoefficientModel.extract c r v (if P then a else b) =
      if P then FormulaSignSlotRadialEliminantCoefficientModel.extract c r v a
      else FormulaSignSlotRadialEliminantCoefficientModel.extract c r v b := by
  split_ifs <;> rfl

private theorem coordinate_coefficient (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (FormulaSignSlotRadialEliminantRows.polynomial c coordinate (CoerciveCriticalHomogenization.layout none)).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (e.mapDomain CoerciveCriticalHomogenization.layout) s t r v) =
        (if s = 0 ∧ t = 1 ∧ e = Finsupp.single none 1 then (if r = 0 ∧ v = 0 then 1 else 0) else 0) -
        (if s = 0 ∧ t = 0 ∧ e = Finsupp.single (some coordinate) 1 then (if r = 0 ∧ v = 0 then 1 else 0) else 0) := by
  rw [FormulaSignSlotRadialEliminantRows.coefficient]
  change FormulaSignSlotRadialEliminantCoefficientModel.extract c r v ((((rename CoerciveCriticalHomogenization.layout
    (TiltedCoerciveCriticalFibers.nativeSystem
      ((FormulaSignSlotRadialFormalCenter.polynomial c).map ParametricTiltedCoerciveEliminant.constants)
      (degreeBudget c) (marginIndex c) Polynomial.X (Polynomial.C Polynomial.X) coordinate none)).coeff
      (e.mapDomain CoerciveCriticalHomogenization.layout)).coeff s).coeff t) = _
  rw [coeff_rename_mapDomain _ CoerciveCriticalHomogenization.layout.injective,
    ParametricTiltedCoerciveCoefficient.coordinate]
  simp only [map_sub, extract_if, map_zero, extract_integer]

theorem coordinateValue_correct (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (i : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) (q : List Bool) :
    coordinateValue read W target head epsilon targetParameter modulus i q =
      residueBits (((FormulaSignSlotRadialEliminantRows.polynomial (read q) (i q)
        (CoerciveCriticalHomogenization.layout none)).coeff
          (FormulaSignSlotRadialEliminantRows.exponent
            ((homogeneousExponent read W target head q).mapDomain CoerciveCriticalHomogenization.layout)
            (Nat.fromBitsLE (epsilon q)) (Nat.fromBitsLE (targetParameter q))
            (FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q))
            (FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q))) : ℤ) :
              ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus q) + 1)))
    (coordinate_coefficient (read q) (i q) (homogeneousExponent read W target head q) _ _ _ _).symm

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
