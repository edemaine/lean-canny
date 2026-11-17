/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedCriticalPolynomial
public import LeanCanny.CountingHierarchy.UnityWeightedSum
public import Mathlib.Tactic.LinearCombination

/-! # Distinct critical values at the initial deformation parameter -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

/-- The separated integer centers used in the manuscript, with indices
 shifted to the zero-based `Fin n` convention. -/
@[expose] def separatedCenters {n : ℕ} (ell : ℕ) (i : Fin n) : ℕ :=
  (4 * ell) ^ (i.val + 1)

/-- At an initial critical point each coordinate is a center times a
 root of unity, and the potential becomes an affine weighted sum. -/
theorem eval_potential_at_unity {S : Type*} [CommRing S] {n : ℕ}
    (ell : ℕ) (a z : Fin n → S) (hz : ∀ i, z i ^ ell = 1) :
    eval (fun i => a i * z i) (potentialPolynomial ell a) =
      (ell + 1 : ℕ) * (∑ i, a i ^ (ell + 1)) -
        (ell : S) * (∑ i, a i ^ (ell + 1) * z i) := by
  rw [potentialPolynomial, map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_add, map_sub, map_mul, map_pow, eval_X, eval_C, mul_pow,
    pow_succ, hz, Nat.cast_add, Nat.cast_one]
  ring

/-- The initial critical values are pairwise distinct. A root-separation
 estimate and Cauchy's bound justify the explicit centers; no generic
 choice of centers or primitive-element oracle is assumed. -/
theorem potential_at_separated_unity_injective {n : ℕ} (ell : ℕ) (hell : 1 ≤ ell)
    (z w : Fin n → ℂ) (hz : ∀ i, z i ^ ell = 1) (hw : ∀ i, w i ^ ell = 1)
    (hvalue : eval (fun i => (separatedCenters ell i : ℂ) * z i)
        (potentialPolynomial ell (fun i => (separatedCenters ell i : ℂ))) =
      eval (fun i => (separatedCenters ell i : ℂ) * w i)
        (potentialPolynomial ell (fun i => (separatedCenters ell i : ℂ)))) : z = w := by
  let R : ℕ := (4 * ell) ^ (ell + 1)
  have hR : 2 * ell + 1 ≤ R := by
    have hbase : 4 * ell ≤ (4 * ell) ^ (ell + 1) :=
      le_self_pow₀ (by omega) (by omega)
    omega
  have hell0 : (ell : ℂ) ≠ 0 := by exact_mod_cast (by omega : ell ≠ 0)
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  rw [eval_potential_at_unity ell _ z hz, eval_potential_at_unity ell _ w hw] at hvalue
  have hprod : (ell : ℂ) * (∑ i, (separatedCenters ell i : ℂ) ^ (ell + 1) * z i) =
      (ell : ℂ) * (∑ i, (separatedCenters ell i : ℂ) ^ (ell + 1) * w i) := by
    linear_combination -hvalue
  have hs := mul_left_cancel₀ hell0 hprod
  have hweight (i : Fin n) : (separatedCenters ell i : ℂ) ^ (ell + 1) =
      (R : ℂ) * (R : ℂ) ^ i.val := by
    change (((4 * ell) ^ (i.val + 1) : ℕ) : ℂ) ^ (ell + 1) = _
    rw [Nat.cast_pow, pow_right_comm, ← Nat.cast_pow]
    change ((R : ℂ) ^ (i.val + 1)) = _
    rw [pow_succ, mul_comm]
  simp_rw [hweight, mul_assoc] at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  exact unity_weightedSum_injective ell (by omega) R hR n z w hz hw (mul_left_cancel₀ hR0 hs)

end LeanCanny.CountingHierarchy
