/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCoordinateCriticalReduction

/-! # Integral Euler row operations with independently supplied gradient lower parts

Common-denominator clearing applies the same spatial degree allowance to
both source and gradient rows. Their lower parts can therefore be supplied
directly, without differentiating a parameter specialization.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerEulerReduction
open MvPolynomial
open FermatCoordinateCriticalReduction (others)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def gradient (a : R) (D : ℕ) (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R := C (a * (D : R)) * X i ^ (D - 1) + g i

noncomputable def objectiveLower (low : MvPolynomial (Fin (n + 1)) R)
    (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R := C (D : R) * low - ∑ i ∈ others r, X i * g i

noncomputable def lower (low : MvPolynomial (Fin (n + 1)) R)
    (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R := if i = r then objectiveLower low g D r else g i

theorem objective_eq (low : MvPolynomial (Fin (n + 1)) R)
    (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (a : R) (D : ℕ) (hD : 0 < D) (r : Fin (n + 1)) :
    C (D : R) * FermatCriticalHomogenization.polynomial low a D - ∑ i ∈ others r, X i * gradient a D g i =
      C (a * (D : R)) * X r ^ D + objectiveLower low g D r := by
  have HP (i : Fin (n + 1)) : (X i : MvPolynomial (Fin (n + 1)) R) * X i ^ (D - 1) = X i ^ D := by
    rw [← pow_succ']
    congr 1
    omega
  have HS : (∑ i ∈ others r, X i * gradient a D g i) =
      C (a * (D : R)) * (∑ i ∈ others r, X i ^ D) + ∑ i ∈ others r, X i * g i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [gradient, mul_add, mul_left_comm (X i), HP]
  have HC : C (D : R) * FermatCriticalHomogenization.polynomial low a D =
      C (D : R) * low + C (a * (D : R)) * ∑ i : Fin (n + 1), X i ^ D := by
    rw [FermatCriticalHomogenization.polynomial, mul_add, ← mul_assoc, ← map_mul, mul_comm (D : R) a]
  have HE : (∑ i : Fin (n + 1), (X i : MvPolynomial (Fin (n + 1)) R) ^ D) =
      (∑ i ∈ others r, X i ^ D) + X r ^ D :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ r)).symm
  rw [HC, HS, HE, objectiveLower]
  ring

theorem lower_degree (low : MvPolynomial (Fin (n + 1)) R)
    (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (D : ℕ) (hD : 2 ≤ D)
    (hlow : low.totalDegree < D) (hg : ∀ i, (g i).totalDegree < D - 1) (r i : Fin (n + 1)) :
    (lower low g D r i).totalDegree < FermatCoordinateCriticalReduction.degrees r D i := by
  by_cases hi : i = r
  · simp only [lower, FermatCoordinateCriticalReduction.degrees, ite_eq_left hi]
    unfold objectiveLower
    apply (totalDegree_sub _ _).trans_lt
    apply max_lt
    · exact (totalDegree_mul _ _).trans_lt (by simpa only [totalDegree_C, Nat.zero_add] using hlow)
    · have HS : (∑ j ∈ others r, X j * g j).totalDegree ≤ D - 1 := by
        apply totalDegree_finsetSum_le
        intro j _
        have HX : (X j : MvPolynomial (Fin (n + 1)) R).totalDegree ≤ 1 := by
          simpa [MvPolynomial.X] using totalDegree_monomial_le (Finsupp.single j 1) (1 : R)
        exact (totalDegree_mul _ _).trans ((Nat.add_le_add_right HX _).trans (by have := hg j; omega))
      exact HS.trans_lt (by omega)
  · simpa only [lower, FermatCoordinateCriticalReduction.degrees, ite_eq_right hi] using hg i

theorem relations_root {K : Type*} [CommRing K] (φ : R →+* K)
    (low : MvPolynomial (Fin (n + 1)) R) (g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (a : R) (D : ℕ) (hD : 0 < D) (r : Fin (n + 1)) (x : Fin (n + 1) → K)
    (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ x = 0)
    (hg : ∀ i, i ≠ r → (gradient a D g i).eval₂ φ x = 0) (i : Fin (n + 1)) :
    (C (a * (D : R)) * X i ^ FermatCoordinateCriticalReduction.degrees r D i + lower low g D r i).eval₂ φ x = 0 := by
  by_cases hi : i = r
  · subst i
    simp only [FermatCoordinateCriticalReduction.degrees, lower, ite_true]
    rw [← objective_eq low g a D hD r, eval₂_sub, eval₂_mul, hp, mul_zero, eval₂_sum]
    rw [Finset.sum_eq_zero]
    · exact sub_self _
    · intro j hj
      rw [eval₂_mul, hg j (Finset.mem_erase.mp hj).1, mul_zero]
  · simpa only [FermatCoordinateCriticalReduction.degrees, lower, ite_eq_right hi, gradient] using hg i hi

end LeanCanny.Algebra.PurePowerEulerReduction
