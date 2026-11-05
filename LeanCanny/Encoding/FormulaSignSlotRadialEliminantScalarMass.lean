/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterSupport
public import LeanCanny.ETR.PolynomialMass
/-! # Original-only scalar heights for actual formal homogeneous row coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantScalarMass
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open FormulaSignSlotRadialEliminantCoefficientModel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalInput.polynomial

noncomputable def sourceSize (c : List Bool) := (FormulaSignSlotRadialFormalInput.equation c).toData.size
noncomputable def denseBound (c : List Bool) := 2 * degreeBudget c * 2 ^ (2 * sourceSize c)
noncomputable def budget (c : List Bool) := 2 * sourceSize c + 2 * degreeBudget c + 4

theorem sourceSize_unary : UnaryFn sourceSize := FormulaSignSlotRadialFormalInput.equation_size_unary
theorem budget_unary : UnaryFn budget :=
  (((UnaryFn.const 2).mul sourceSize_unary).add ((UnaryFn.const 2).mul degreeBudget_unary)).add (UnaryFn.const 4)

theorem source_mass (c : List Bool) : MvMass.mass (FormulaSignSlotRadialFormalInput.polynomial c) ≤ 2 ^ sourceSize c := by
  have H := (FormulaSignSlotRadialFormalInput.equation c).finitePolynomial_mass
    (FormulaSignSlotRadialFormalInput.dimension c)
  rw [FormulaSignSlotRadialFormalInput.finitePolynomial_eq] at H
  exact H

theorem dense_abs (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Fin (FormulaSignSlotRadialFormalInput.spatial c) →₀ ℕ) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (dense c j e r v).natAbs ≤ denseBound c := by
  let q := FormulaSignSlotRadialFormalInput.polynomial c
  have HD : (q ^ 2).totalDegree ≤ 2 * degreeBudget c :=
    (totalDegree_pow q 2).trans (Nat.mul_le_mul_left 2 (FormulaSignSlotRadialFormalInput.polynomial_degree c))
  have HM : MvMass.mass (q ^ 2) ≤ (2 ^ sourceSize c) ^ 2 :=
    (MvMass.pow_le q 2).trans (Nat.pow_le_pow_left (source_mass c) 2)
  exact (MvMass.coeff_le _ _).trans ((MvMass.pderiv_le (q ^ 2) _).trans
    ((Nat.mul_le_mul HD HM).trans_eq (by unfold denseBound; rw [← pow_mul]; congr 2; omega)))

private theorem ite_abs_le (P : Prop) [Decidable P] (z : ℤ) (B : ℕ) (hz : z.natAbs ≤ B) :
    (if P then z else 0).natAbs ≤ B := by
  by_cases HP : P
  · simpa only [HP, ite_true] using hz
  · simp only [HP, ite_false, Int.natAbs_zero, Nat.zero_le]

theorem gradient_abs (c : List Bool) (j : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (gradient c j e s t r v).natAbs ≤ denseBound c + 2 * degreeBudget c + 3 := by
  have HD := ite_abs_le (s = 0 ∧ t = 0) _ _ (dense_abs c j e.some r v)
  have HT := ite_abs_le (j = marginIndex c) _ _
    (ite_abs_le (e.some = 0) _ _ (ite_abs_le (s = 1 ∧ t = 0) _ _
      (ite_abs_le (r = 0 ∧ v = 0) (1 : ℤ) 1 (by decide))))
  have HL := ite_abs_le (Finsupp.single (some j) (2 * degreeBudget c + 1) = e) _ _
    (ite_abs_le (s = 2 ∧ t = 0) _ _ (ite_abs_le (r = 0 ∧ v = 0)
      ((2 * degreeBudget c + 2 : ℕ) : ℤ) (2 * degreeBudget c + 2)
      (by rw [Int.natAbs_natCast])))
  have HB := ite_abs_le
    (Finsupp.weight (WeightedHomogenization.weights (fun _ : Fin (FormulaSignSlotRadialFormalInput.spatial c) => 1)) e = 2 * degreeBudget c + 1)
    _ _ ((Int.natAbs_sub_le _ _).trans (Nat.add_le_add HD HT))
  exact ((Int.natAbs_add_le _ _).trans (Nat.add_le_add HB HL)).trans (by omega)

private theorem extract_one_abs (c : List Bool) (r : ℕ) (v : Fin (d c) →₀ ℕ) :
    (extract c r v (1 : FormulaSignSlotRadialFormalCenter.Radius c)).natAbs ≤ 1 := by
  change ((((1 : Polynomial (MvPolynomial (Fin (d c)) ℤ)).coeff r).coeff v)).natAbs ≤ 1
  by_cases HR : r = 0
  · subst r
    rw [Polynomial.coeff_one_zero, MvPolynomial.coeff_one]
    split_ifs <;> decide
  · rw [Polynomial.coeff_one, ite_eq_right HR]
    simp

private theorem small_difference (P Q : Prop) [Decidable P] [Decidable Q] (z : ℤ) (hz : z.natAbs ≤ 1) :
    ((if P then z else 0) - (if Q then z else 0)).natAbs ≤ 1 := by
  by_cases HP : P <;> by_cases HQ : Q
  · simp only [HP, HQ, ite_true, sub_self, Int.natAbs_zero, Nat.zero_le]
  · simpa only [HP, HQ, ite_true, ite_false, sub_zero] using hz
  · simpa only [HP, HQ, ite_true, ite_false, zero_sub, Int.natAbs_neg] using hz
  · simp only [HP, HQ, ite_false, sub_self, Int.natAbs_zero, Nat.zero_le]

theorem coordinate_abs (c : List Bool) (coordinate : Fin (FormulaSignSlotRadialFormalInput.spatial c))
    (e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial c)) →₀ ℕ)
    (s t r : ℕ) (v : Fin (d c) →₀ ℕ) :
    ((FormulaSignSlotRadialEliminantRows.polynomial c coordinate (CoerciveCriticalHomogenization.layout none)).coeff
      (FormulaSignSlotRadialEliminantRows.exponent (e.mapDomain CoerciveCriticalHomogenization.layout) s t r v)).natAbs ≤ 1 := by
  rw [FormulaSignSlotRadialEliminantRows.coefficient]
  change (extract c r v ((((rename CoerciveCriticalHomogenization.layout
    (TiltedCoerciveCriticalFibers.nativeSystem
      ((FormulaSignSlotRadialFormalCenter.polynomial c).map ParametricTiltedCoerciveEliminant.constants)
      (degreeBudget c) (marginIndex c) Polynomial.X (Polynomial.C Polynomial.X) coordinate none)).coeff
      (e.mapDomain CoerciveCriticalHomogenization.layout)).coeff s).coeff t)).natAbs ≤ 1
  rw [coeff_rename_mapDomain _ CoerciveCriticalHomogenization.layout.injective,
    ParametricTiltedCoerciveCoefficient.coordinate, map_sub]
  simpa only [apply_ite (extract c r v), map_zero] using
    small_difference _ _ (extract c r v 1) (extract_one_abs c r v)

theorem scalar_budget (c : List Bool) : denseBound c + 2 * degreeBudget c + 3 ≤ 2 ^ budget c := by
  let A := 2 * degreeBudget c + 3
  have HM : 1 ≤ 2 ^ (2 * sourceSize c) := Nat.one_le_two_pow
  have HA : A ≤ 2 ^ A := Nat.lt_two_pow_self.le
  calc
    _ ≤ 2 * (A * 2 ^ (2 * sourceSize c)) := by
      unfold denseBound A
      nlinarith
    _ ≤ 2 * (2 ^ A * 2 ^ (2 * sourceSize c)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ HA)
    _ = 2 ^ budget c := by
      rw [← pow_add, mul_comm, ← pow_succ]
      congr 1
      unfold A budget
      omega

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantScalarMass
