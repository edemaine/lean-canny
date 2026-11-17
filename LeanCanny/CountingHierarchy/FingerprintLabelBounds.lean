/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintLabelPolynomial
public import LeanCanny.CountingHierarchy.ClearedSignTestBounds

/-! # Uniform degree and mass bounds for fingerprint labels -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

def fingerprintLabelDegreeBound (m B s D : ℕ) : ℕ := 2 * ((m + 2) * signTestDegreeBound B s D)
def fingerprintLabelMassExponent (m B s b W : ℕ) : ℕ :=
  2 * (W.size + (m + 2) * signTestMassExponent B s b + 1) + 5

theorem fingerprintLabelPolynomial_degree_le {m : ℕ} (B s D b : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ)
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b) :
    (fingerprintLabelPolynomial B s g w target).natDegree ≤ fingerprintLabelDegreeBound m B s D := by
  let K := (m + 2) * signTestDegreeBound B s D
  have hE : (signTestCommonDenominator B s g).natDegree ≤ K :=
    (signTestCommonDenominator_bounds B s D b g hD hb).1.trans
      (Nat.mul_le_mul_right _ (by omega))
  have hT (i) : (signTestClearedNumerator B s g i).natDegree ≤ K :=
    (signTestClearedNumerator_bounds B s D b g hD hb i).1
  have hCE (z : ℤ) : (C z * signTestCommonDenominator B s g).natDegree ≤ K :=
    Polynomial.natDegree_mul_le.trans (by simpa only [natDegree_C, Nat.zero_add] using hE)
  have hS : (∑ i : Fin m, C (w i : ℤ) * signTestClearedNumerator B s g i.succ).natDegree ≤ K := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact Polynomial.natDegree_mul_le.trans (by simpa only [natDegree_C, Nat.zero_add] using hT i.succ)
  have hp (A : Polynomial ℤ) (hA : A.natDegree ≤ K) : (C (4 : ℤ) * A ^ 2).natDegree ≤ 2 * K := by
    apply Polynomial.natDegree_mul_le.trans
    simpa only [natDegree_C, Nat.zero_add] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hA)
  unfold fingerprintLabelPolynomial fingerprintLabelDegreeBound
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le
      (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hE))
      (hp _ ((natDegree_sub_le _ _).trans (max_le hS (hCE target))))))
    (hp _ ((natDegree_sub_le _ _).trans (max_le (hT 0) hE))))

theorem fingerprintLabelPolynomial_mass_le {m : ℕ} (B s D b W : ℕ)
    (g : Fin (m + 1) → Polynomial ℤ) (w : Fin m → ℕ) (target : ℤ)
    (hD : ∀ i, (g i).natDegree ≤ D) (hb : ∀ i, coefficientMass (g i) ≤ 2 ^ b)
    (hw : ∑ i, w i ≤ W) (ht : target.natAbs ≤ W) :
    coefficientMass (fingerprintLabelPolynomial B s g w target) ≤
      2 ^ fingerprintLabelMassExponent m B s b W := by
  let T := (m + 2) * signTestMassExponent B s b
  let E := signTestCommonDenominator B s g
  let N := signTestClearedNumerator B s g
  have hE : coefficientMass E ≤ 2 ^ T :=
    (signTestCommonDenominator_bounds B s D b g hD hb).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have hN (i) : coefficientMass (N i) ≤ 2 ^ T :=
    (signTestClearedNumerator_bounds B s D b g hD hb i).2
  have hS : coefficientMass (∑ i : Fin m, C (w i : ℤ) * N i.succ) ≤ 2 ^ (W.size + T) := by
    apply (coefficientMass_sum_le _ _).trans
    calc
      _ ≤ ∑ i : Fin m, w i * 2 ^ T := by
        apply Finset.sum_le_sum
        intro i _
        apply (coefficientMass_mul_le _ _).trans
        simpa only [coefficientMass_C, Int.natAbs_natCast] using Nat.mul_le_mul_left (w i) (hN i.succ)
      _ = (∑ i, w i) * 2 ^ T := (Finset.sum_mul _ _ _).symm
      _ ≤ 2 ^ W.size * 2 ^ T := Nat.mul_le_mul_right _ (hw.trans (Nat.lt_size_self W).le)
      _ = _ := (pow_add 2 _ _).symm
  have htarget : coefficientMass (C target * E) ≤ 2 ^ (W.size + T) := by
    apply (coefficientMass_mul_le _ _).trans
    rw [coefficientMass_C]
    exact (Nat.mul_le_mul (ht.trans (Nat.lt_size_self W).le) hE).trans_eq (pow_add 2 _ _).symm
  let U := W.size + T + 1
  have hdiff : coefficientMass ((∑ i : Fin m, C (w i : ℤ) * N i.succ) - C target * E) ≤ 2 ^ U := by
    apply (coefficientMass_sub_le _ _).trans
    apply (Nat.add_le_add hS htarget).trans
    rw [show U = W.size + T + 1 from rfl, pow_succ]
    omega
  have hzero : coefficientMass (N 0 - E) ≤ 2 ^ U := by
    apply (coefficientMass_sub_le _ _).trans
    have hpow : 2 ^ T ≤ 2 ^ (W.size + T) := Nat.pow_le_pow_right (by decide) (by omega)
    apply (Nat.add_le_add ((hN 0).trans hpow) (hE.trans hpow)).trans
    rw [show U = W.size + T + 1 from rfl, pow_succ]
    omega
  have hquad (A : Polynomial ℤ) (hA : coefficientMass A ≤ 2 ^ U) :
      coefficientMass (C (4 : ℤ) * A ^ 2) ≤ 2 ^ (2 * U + 2) := by
    apply (coefficientMass_mul_le _ _).trans
    rw [coefficientMass_C]
    change 4 * coefficientMass (A ^ 2) ≤ _
    apply (Nat.mul_le_mul_left 4 ((coefficientMass_pow_le _ _).trans (Nat.pow_le_pow_left hA 2))).trans_eq
    rw [← pow_mul, Nat.mul_comm U 2, pow_add]
    omega
  have hfirst : coefficientMass (E ^ 2) ≤ 2 ^ (2 * U + 2) := by
    apply (coefficientMass_pow_le _ _).trans
    apply (Nat.pow_le_pow_left hE 2).trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [U]; omega)
  change coefficientMass (E ^ 2 - C 4 * ((∑ i, C (w i : ℤ) * N i.succ) - C target * E) ^ 2 -
    C 4 * (N 0 - E) ^ 2) ≤ _
  apply (coefficientMass_sub_le _ _).trans
  apply (Nat.add_le_add ((coefficientMass_sub_le _ _).trans
    (Nat.add_le_add hfirst (hquad _ hdiff))) (hquad _ hzero)).trans
  change 2 ^ (2 * U + 2) + 2 ^ (2 * U + 2) + 2 ^ (2 * U + 2) ≤ 2 ^ (2 * U + 5)
  rw [show 2 * U + 5 = (2 * U + 2) + 3 by omega]
  simp only [pow_add, Nat.reducePow]
  omega

end LeanCanny.CountingHierarchy
