/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteCriticalCriterion
public import LeanCanny.CountingHierarchy.FiniteCriticalMassBounds

/-! # A short logarithmic bound for the actual feasibility determinant -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra

@[expose] noncomputable def finiteCriticalShiftedLabel {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) : Polynomial ℤ :=
  shiftedIntegerLabel ((d + 1) ^ n) e
    (sparseIntegerRootLabel (finiteCriticalPolynomial d b F hF)
      (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X)
      (criticalRootLabelLength n d) (criticalLabelInputMassExponent n d b) L)

@[expose] noncomputable def finiteCriticalNormObjective {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) : MvPolynomial (Fin n) ℤ :=
  Polynomial.aeval (finiteCriticalObjective d b F) (finiteCriticalShiftedLabel d b F hF L e)

/-- The budgets are independent of the contents or length of the label list. -/
theorem finiteCriticalShiftedLabel_bounds {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) (he : e ≤ (d + 1) ^ n) :
    (finiteCriticalShiftedLabel d b F hF L e).natDegree ≤ criticalShiftedLabelDegreeBound n d b ∧
      coefficientMass (finiteCriticalShiftedLabel d b F hF L e) ≤
        2 ^ criticalShiftedLabelMassExponent n d b := by
  have hD : (finiteCriticalPolynomial d b F hF).natDegree ≤ (d + 1) ^ n := by
    rw [finiteCriticalPolynomial_eq_charpoly d hd b F hF,
      Matrix.charpoly_natDegree_eq_dim, card_normalIndex]
  have hpos : 1 ≤ (d + 1) ^ n := Nat.one_le_pow _ _ (by omega)
  have hR : (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X).natDegree ≤ (d + 1) ^ n := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    exact max_le (Nat.zero_le _) hpos
  have hlabel := sparseIntegerRootLabel_bounds (finiteCriticalPolynomial d b F hF)
    (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X)
    (criticalRootLabelLength n d) (criticalLabelInputMassExponent n d b) L hD hR
    (finiteCriticalPolynomial_mass_le d hd b F hF hM) (criticalCutoff_test_mass_le n d b)
  exact ⟨(shiftedIntegerLabel_degree_le _ _ _).trans hlabel.1,
    shiftedIntegerLabel_mass_le _ e _ _ he hlabel.2⟩

theorem finiteCriticalNormObjective_bounds {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) (he : e ≤ (d + 1) ^ n) :
    (finiteCriticalNormObjective d b F hF L e).totalDegree ≤ criticalNormObjectiveDegreeBound n d b ∧
      MvMass.mass (finiteCriticalNormObjective d b F hF L e) ≤
        2 ^ criticalNormObjectiveMassExponent n d b := by
  have hlabel := finiteCriticalShiftedLabel_bounds d hd b F hF hM L e he
  exact ⟨polynomial_aeval_degree_le _ _ _ _ hlabel.1 (finiteCriticalObjective_degree_le d b F hF),
    polynomial_aeval_mass_le_pow _ _ _ _ _ hlabel.1 hlabel.2 (finiteCriticalObjective_mass_le d b F hM)⟩

/-- This is a bound for the integer determinant appearing in the proved
finite feasibility criterion, with no bound or matrix supplied by an oracle. -/
theorem finiteCriticalDeterminant_natAbs_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (hM : MvMass.mass F ≤ 2 ^ b)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) (he : e ≤ (d + 1) ^ n) :
    (finiteCriticalDeterminant d b F hF L e).natAbs ≤ 2 ^ criticalNormMassExponent n d b := by
  have hobj := finiteCriticalNormObjective_bounds d hd b F hF hM L e he
  exact multiplicationMatrix_det_natAbs_le d hd (finiteCriticalRelations d b F)
    (finiteCriticalRelations_degree d b F hF) (finiteCriticalNormObjective d b F hF L e)
    _ _ _ hobj.1 hobj.2 (finiteCriticalRelations_mass_le d b F hF hM)

end LeanCanny.CountingHierarchy
