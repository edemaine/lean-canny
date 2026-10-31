/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalHomogenization
public import LeanCanny.Algebra.PurePowerRelativeAnnihilator

/-! # Pure-power relations for coordinate critical points

An integral row operation replaces the source equation by D times the source
minus the nonobjective Euler terms. Its leading monomial is the objective
coordinate's Dth power. The remaining gradient rows have pure powers of
degree D-1, all with the same leading coefficient a*D. No division is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCoordinateCriticalReduction
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def others (r : Fin (n + 1)) : Finset (Fin (n + 1)) := Finset.univ.erase r

def degrees (r : Fin (n + 1)) (D : ℕ) (i : Fin (n + 1)) : ℕ := if i = r then D else D - 1

noncomputable def lowerObjective (low : MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R := C (D : R) * low - ∑ i ∈ others r, X i * pderiv i low

noncomputable def lower (low : MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R := if i = r then lowerObjective low D r else pderiv i low

noncomputable def objectiveRow (p : MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R := C (D : R) * p - ∑ i ∈ others r, X i * pderiv i p

theorem objective_eq (low : MvPolynomial (Fin (n + 1)) R) (a : R) (D : ℕ)
    (hD : 0 < D) (r : Fin (n + 1)) :
    objectiveRow (FermatCriticalHomogenization.polynomial low a D) D r =
      C (a * (D : R)) * X r ^ D + lowerObjective low D r := by
  have HP (i : Fin (n + 1)) : (X i : MvPolynomial (Fin (n + 1)) R) * X i ^ (D - 1) = X i ^ D := by
    rw [← pow_succ']
    congr 1
    omega
  have HS : (∑ i ∈ others r, X i * pderiv i (FermatCriticalHomogenization.polynomial low a D)) =
      (∑ i ∈ others r, X i * pderiv i low) + C (a * (D : R)) * ∑ i ∈ others r, X i ^ D := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [FermatCriticalHomogenization.pderiv_polynomial, mul_add, mul_left_comm (X i), HP]
  have HC : C (D : R) * FermatCriticalHomogenization.polynomial low a D =
      C (D : R) * low + C (a * (D : R)) * ∑ i : Fin (n + 1), X i ^ D := by
    rw [FermatCriticalHomogenization.polynomial, mul_add, ← mul_assoc, ← map_mul, mul_comm (D : R) a]
  have HE : (∑ i : Fin (n + 1), (X i : MvPolynomial (Fin (n + 1)) R) ^ D) =
      (∑ i ∈ others r, X i ^ D) + X r ^ D :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ r)).symm
  rw [objectiveRow, HC, HS, HE, lowerObjective]
  ring

theorem lower_degree (low : MvPolynomial (Fin (n + 1)) R) (D : ℕ) (hD : 2 ≤ D)
    (hlow : low.totalDegree < D) (r i : Fin (n + 1)) : (lower low D r i).totalDegree < degrees r D i := by
  have HG (j : Fin (n + 1)) : (pderiv j low).totalDegree < D - 1 :=
    (PartialDerivativeDegree.degree_le low j).trans_lt (by omega)
  by_cases hi : i = r
  · rw [lower, ite_eq_left hi, degrees, ite_eq_left hi, lowerObjective]
    apply (totalDegree_sub _ _).trans_lt
    apply max_lt
    · exact (totalDegree_mul _ _).trans_lt (by simpa only [totalDegree_C, Nat.zero_add] using hlow)
    · have HS : (∑ j ∈ others r, X j * pderiv j low).totalDegree ≤ D - 1 := by
        apply totalDegree_finsetSum_le
        intro j _
        have HX : (X j : MvPolynomial (Fin (n + 1)) R).totalDegree ≤ 1 := by
          simpa [MvPolynomial.X] using
            totalDegree_monomial_le (Finsupp.single j 1) (1 : R)
        exact (totalDegree_mul _ _).trans ((Nat.add_le_add_right HX _).trans (by have := HG j; omega))
      exact HS.trans_lt (by omega)
  · simpa only [lower, degrees, ite_eq_right hi] using HG i

theorem objective_root {K : Type*} [CommRing K] (φ : R →+* K)
    (p : MvPolynomial (Fin (n + 1)) R) (D : ℕ) (r : Fin (n + 1)) (x : Fin (n + 1) → K)
    (hp : p.eval₂ φ x = 0) (hx : ∀ i, i ≠ r → (pderiv i p).eval₂ φ x = 0) :
    (objectiveRow p D r).eval₂ φ x = 0 := by
  simp only [objectiveRow, eval₂_sub, eval₂_mul, hp, mul_zero, eval₂_sum]
  rw [Finset.sum_eq_zero]
  · exact sub_self _
  · intro i hi
    rw [hx i (Finset.mem_erase.mp hi).1, mul_zero]

theorem relations_root {K : Type*} [CommRing K] (φ : R →+* K)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (D : ℕ) (hD : 0 < D) (r : Fin (n + 1))
    (x : Fin (n + 1) → K) (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ x = 0)
    (hx : ∀ i, i ≠ r → (pderiv i (FermatCriticalHomogenization.polynomial low a D)).eval₂ φ x = 0)
    (i : Fin (n + 1)) :
    (C (a * (D : R)) * X i ^ degrees r D i + lower low D r i).eval₂ φ x = 0 := by
  by_cases hi : i = r
  · subst i
    simp only [degrees, lower, ite_true]
    rw [← objective_eq low a D hD r]
    exact objective_root φ _ D r x hp hx
  · simp only [degrees, lower, ite_eq_right hi]
    rw [add_comm (C (a * (D : R)) * X i ^ (D - 1)) (pderiv i low),
      ← FermatCriticalHomogenization.pderiv_polynomial]
    exact hx i hi

theorem coordinate_annihilator_root {B : ℕ} {K : Type*} [Field K] (φ : R →+* K)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (D : ℕ) (hD : 2 ≤ D)
    (hlow : low.totalDegree < D) (r : Fin (n + 1)) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound (degrees r D) + 1 ≤ bound) (hbound : bound < 2 ^ B)
    (x : Fin (n + 1) → K) (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ x = 0)
    (hx : ∀ i, i ≠ r → (pderiv i (FermatCriticalHomogenization.polynomial low a D)).eval₂ φ x = 0)
    (j : Fin (n + 1)) :
    (PurePowerRelativeAnnihilator.polynomial r (degrees r D) (lower low D r)
      (a * (D : R)) bound hgrid hbound j).eval₂ φ (x j) = 0 := by
  have HD : ∀ i, 0 < degrees r D i := by
    intro i
    unfold degrees
    split_ifs <;> omega
  exact PurePowerRelativeAnnihilator.root φ r _ HD _ (lower_degree low D hD hlow r)
    _ bound hgrid hbound j x (relations_root φ low a D (by omega) r x hp hx)

end LeanCanny.Algebra.FermatCoordinateCriticalReduction
