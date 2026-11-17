/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ClearedSignTests
public import LeanCanny.CountingHierarchy.PolynomialCompositionMass

/-! # Degree and mass budgets for positive-denominator clearing -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

@[expose] def signTestDegreeBound (B s D : ℕ) : ℕ := 2 * s * (2 * B + 1) * D

@[expose] def signTestMassExponent (B s b : ℕ) : ℕ :=
  2 * s * (2 * B + 1) * (B + 1) + 2 * s * (2 * B + 1) * b + 1

theorem signTest_bounds (B s D b : ℕ) (g : Polynomial ℤ)
    (hD : g.natDegree ≤ D) (hb : coefficientMass g ≤ 2 ^ b) :
    (signTestDenominator B s g).natDegree ≤ signTestDegreeBound B s D ∧
      (signTestNumerator B s g).natDegree ≤ signTestDegreeBound B s D ∧
      coefficientMass (signTestDenominator B s g) ≤ 2 ^ signTestMassExponent B s b ∧
      coefficientMass (signTestNumerator B s g) ≤ 2 ^ signTestMassExponent B s b := by
  let c := 2 * s * (2 * B + 1)
  have hd (q : Polynomial ℤ) (hq : q.natDegree ≤ D) :
      ((rationalSignProduct B s).comp q).natDegree ≤ c * D :=
    Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul (rationalSignProduct_natDegree_le B s) hq)
  have hm (q : Polynomial ℤ) (hq : coefficientMass q ≤ 2 ^ b) :
      coefficientMass ((rationalSignProduct B s).comp q) ≤ 2 ^ (c * (B + 1) + c * b) :=
    coefficientMass_comp_le_pow _ q c (c * (B + 1)) b
      (rationalSignProduct_natDegree_le B s) (rationalSignProduct_mass_le B s) hq
  have hdneg : (-g).natDegree ≤ D := by simpa only [Polynomial.natDegree_neg] using hD
  have hmneg : coefficientMass (-g) ≤ 2 ^ b := by simpa only [coefficientMass_neg] using hb
  have hsum : 2 ^ (c * (B + 1) + c * b) + 2 ^ (c * (B + 1) + c * b) ≤
      2 ^ signTestMassExponent B s b := by
    rw [signTestMassExponent, pow_succ]
    dsimp only [c]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le (hd g hD) (hd (-g) hdneg))
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hd g hD) (hd (-g) hdneg))
  · exact (coefficientMass_add_le _ _).trans ((Nat.add_le_add (hm g hb) (hm (-g) hmneg)).trans hsum)
  · exact (coefficientMass_sub_le _ _).trans ((Nat.add_le_add (hm g hb) (hm (-g) hmneg)).trans hsum)

theorem signTestCommonDenominator_bounds {m : ℕ} (B s D b : ℕ)
    (g : Fin m → Polynomial ℤ) (hD : ∀ i, (g i).natDegree ≤ D)
    (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b) :
    (signTestCommonDenominator B s g).natDegree ≤ m * signTestDegreeBound B s D ∧
      coefficientMass (signTestCommonDenominator B s g) ≤ 2 ^ (m * signTestMassExponent B s b) := by
  constructor
  · apply (Polynomial.natDegree_prod_le _ _).trans
    exact (Finset.sum_le_sum (fun i _ => (signTest_bounds B s D b (g i) (hD i) (hb i)).1)).trans_eq (by simp)
  · apply (coefficientMass_prod_le _ _).trans
    exact (Finset.prod_le_prod (fun i _ => (signTest_bounds B s D b (g i) (hD i) (hb i)).2.2.1)).trans_eq
      (by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm])

theorem signTestClearedNumerator_bounds {m : ℕ} (B s D b : ℕ)
    (g : Fin m → Polynomial ℤ) (hD : ∀ i, (g i).natDegree ≤ D)
    (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b) (i : Fin m) :
    (signTestClearedNumerator B s g i).natDegree ≤ (m + 1) * signTestDegreeBound B s D ∧
      coefficientMass (signTestClearedNumerator B s g i) ≤ 2 ^ ((m + 1) * signTestMassExponent B s b) := by
  have hcard : (Finset.univ.erase i).card ≤ m := by
    simpa only [Finset.card_univ, Fintype.card_fin] using (Finset.card_erase_le (s := Finset.univ) (a := i))
  have hpdeg : (∏ j ∈ Finset.univ.erase i, signTestDenominator B s (g j)).natDegree ≤
      m * signTestDegreeBound B s D := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply (Finset.sum_le_sum (fun j _ => (signTest_bounds B s D b (g j) (hD j) (hb j)).1)).trans
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using Nat.mul_le_mul_right _ hcard
  have hpmass : coefficientMass (∏ j ∈ Finset.univ.erase i, signTestDenominator B s (g j)) ≤
      2 ^ (m * signTestMassExponent B s b) := by
    apply (coefficientMass_prod_le _ _).trans
    apply (Finset.prod_le_prod (fun j _ => (signTest_bounds B s D b (g j) (hD j) (hb j)).2.2.1)).trans
    simp only [Finset.prod_const, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  constructor
  · exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add (signTest_bounds B s D b (g i) (hD i) (hb i)).2.1 hpdeg).trans_eq (by ring))
  · exact (coefficientMass_mul_le _ _).trans
      ((Nat.mul_le_mul (signTest_bounds B s D b (g i) (hD i) (hb i)).2.2.2 hpmass).trans_eq
        (by rw [← pow_add]; congr 1; ring))

end LeanCanny.CountingHierarchy
