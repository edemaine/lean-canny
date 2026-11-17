/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RootLabelPolynomial
public import LeanCanny.CountingHierarchy.ClearedSignTestBounds

/-! # Uniform degree and log-mass bounds for integer sign-list labels -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

@[expose] def rootLabelDegreeBound (m B s D : ℕ) : ℕ :=
  2 * ((m + 1) * signTestDegreeBound B s D)

@[expose] def rootLabelMassExponent (m B s b : ℕ) : ℕ :=
  m.size + 2 * ((m + 1) * signTestMassExponent B s b) + 5

theorem rootLabelPolynomial_degree_le {m : ℕ} (B s D b : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType)
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b) :
    (rootLabelPolynomial B s g t).natDegree ≤ rootLabelDegreeBound m B s D := by
  let K := signTestDegreeBound B s D
  have hE := (signTestCommonDenominator_bounds B s D b g hD hb).1
  have hT (i : Fin m) := (signTestClearedNumerator_bounds B s D b g hD hb i).1
  have hEm : (signTestCommonDenominator B s g).natDegree ≤ (m + 1) * K :=
    hE.trans (Nat.mul_le_mul_right K (Nat.le_succ m))
  rw [rootLabelPolynomial]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hEm)
  · apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, Nat.zero_add]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Polynomial.natDegree_pow_le.trans
    apply Nat.mul_le_mul_left 2
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (hT i) _
    exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Nat.zero_add] using hEm)

theorem rootLabelPolynomial_mass_le {m : ℕ} (B s D b : ℕ)
    (g : Fin m → Polynomial ℤ) (t : Fin m → SignType)
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b) :
    coefficientMass (rootLabelPolynomial B s g t) ≤ 2 ^ rootLabelMassExponent m B s b := by
  let H := signTestMassExponent B s b
  let T := (m + 1) * H
  let E := signTestCommonDenominator B s g
  have hE : coefficientMass E ≤ 2 ^ T :=
    (signTestCommonDenominator_bounds B s D b g hD hb).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right H (Nat.le_succ m)))
  have hTi (i : Fin m) : coefficientMass (signTestClearedNumerator B s g i) ≤ 2 ^ T :=
    (signTestClearedNumerator_bounds B s D b g hD hb i).2
  have ht (i : Fin m) : coefficientMass (Polynomial.C (t i : ℤ)) ≤ 1 := by
    rw [coefficientMass_C]
    generalize t i = c
    cases c <;> decide
  have hdiff (i : Fin m) : coefficientMass
      (signTestClearedNumerator B s g i - Polynomial.C (t i : ℤ) * E) ≤ 2 ^ (T + 1) := by
    apply (coefficientMass_sub_le _ _).trans
    have htarget : coefficientMass (Polynomial.C (t i : ℤ) * E) ≤ 2 ^ T :=
      (coefficientMass_mul_le _ _).trans ((Nat.mul_le_mul (ht i) hE).trans_eq (Nat.one_mul _))
    apply (Nat.add_le_add (hTi i) htarget).trans
    rw [pow_succ]
    omega
  have hsquare (i : Fin m) : coefficientMass
      ((signTestClearedNumerator B s g i - Polynomial.C (t i : ℤ) * E) ^ 2) ≤ 2 ^ (2 * (T + 1)) :=
    (coefficientMass_pow_le _ _).trans ((Nat.pow_le_pow_left (hdiff i) 2).trans_eq (by
      rw [← pow_mul, Nat.mul_comm]))
  have hsum : coefficientMass (∑ i, (signTestClearedNumerator B s g i - Polynomial.C (t i : ℤ) * E) ^ 2) ≤
      2 ^ (m.size + 2 * (T + 1)) := by
    apply (coefficientMass_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => hsquare i)).trans
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    exact (Nat.mul_le_mul_right _ (Nat.lt_size_self m).le).trans_eq (pow_add 2 _ _).symm
  have hscore : coefficientMass (Polynomial.C (4 : ℤ) *
      ∑ i, (signTestClearedNumerator B s g i - Polynomial.C (t i : ℤ) * E) ^ 2) ≤
      2 ^ (m.size + 2 * T + 4) := by
    apply (coefficientMass_mul_le _ _).trans
    rw [coefficientMass_C]
    change 4 * _ ≤ _
    exact (Nat.mul_le_mul_left 4 hsum).trans_eq (by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]
      congr 1
      omega)
  have hfirst : coefficientMass (E ^ 2) ≤ 2 ^ (m.size + 2 * T + 4) := by
    apply (coefficientMass_pow_le _ _).trans
    apply (Nat.pow_le_pow_left hE 2).trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply (coefficientMass_sub_le _ _).trans
  apply (Nat.add_le_add hfirst hscore).trans
  rw [rootLabelMassExponent, pow_succ]
  change 2 ^ (m.size + 2 * T + 4) + 2 ^ (m.size + 2 * T + 4) ≤
    2 ^ (m.size + 2 * T + 4) * 2
  omega

end LeanCanny.CountingHierarchy
