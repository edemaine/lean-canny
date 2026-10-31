/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionMatrix

/-! # Coordinate multiplication inside the fixed-width reduction grid

Normal monomials have degree at most the sum of the pure-power degree caps
minus one in each coordinate. Adding a coordinate stays inside one larger
degree cap and hence inside the explicit fixed-width state space.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionMatrix
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n B : ℕ}

def gridBound (d : Fin n → ℕ) : ℕ := Finset.univ.sum (fun i => d i - 1)

theorem normal_degree (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : Normal d e) : e.degree ≤ gridBound d := by
  rw [Finsupp.degree_eq_sum, gridBound]
  apply Finset.sum_le_sum
  intro i _
  change e i ≤ d i - 1
  have H : e i < d i := he i
  omega

noncomputable def zeroIndex (n B : ℕ) : Index n B :=
  FixedWidthPolynomial.index n B 0 (fun _ => pow_pos (by decide : 0 < (2 : ℕ)) B)

theorem vector_zero : FixedWidthPolynomial.vector n B (zeroIndex n B) = 0 :=
  FixedWidthPolynomial.vector_index _ _ _ _

theorem shifted_bound (d : Fin n → ℕ) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound)
    (hbound : bound < 2 ^ B) (r : Fin n) (e : Fin n →₀ ℕ) (he : Normal d e) (i : Fin n) :
    (e + Finsupp.single r 1 : Fin n →₀ ℕ) i < 2 ^ B := by
  have HD : (e + Finsupp.single r 1).degree ≤ bound := by
    rw [map_add, Finsupp.degree_single]
    exact (Nat.add_le_add_right (normal_degree d e he) 1).trans hgrid
  exact (Finsupp.le_degree i _).trans_lt (HD.trans_lt hbound)

noncomputable def shift (d : Fin n → ℕ) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound)
    (hbound : bound < 2 ^ B) (r : Fin n) (j : Index n B) : Index n B :=
  if hj : Normal d (FixedWidthPolynomial.vector n B j) then
    FixedWidthPolynomial.index n B (FixedWidthPolynomial.vector n B j + Finsupp.single r 1)
      (shifted_bound d bound hgrid hbound r _ hj)
  else zeroIndex n B

theorem vector_shift (d : Fin n → ℕ) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound)
    (hbound : bound < 2 ^ B) (r : Fin n) (j : Index n B) (hj : Normal d (FixedWidthPolynomial.vector n B j)) :
    FixedWidthPolynomial.vector n B (shift d bound hgrid hbound r j) =
      FixedWidthPolynomial.vector n B j + Finsupp.single r 1 := by
  rw [shift, dite_eq_left hj, FixedWidthPolynomial.vector_index]

variable {R L : Type*} [CommRing R] [CommRing L]

theorem evaluation_shift (φ : R →+* L) (d : Fin n → ℕ) (bound : ℕ) (hgrid : gridBound d + 1 ≤ bound)
    (hbound : bound < 2 ^ B) (r : Fin n) (x : Fin n → L) (j : Index n B)
    (hj : Normal d (FixedWidthPolynomial.vector n B j)) :
    evaluation φ bound x (shift d bound hgrid hbound r j) = x r * evaluation φ bound x j := by
  have HD := normal_degree d (FixedWidthPolynomial.vector n B j) hj
  have HV : (FixedWidthPolynomial.vector n B j).degree ≤ bound := by omega
  have HS : (FixedWidthPolynomial.vector n B j + Finsupp.single r 1).degree ≤ bound := by
    rw [map_add, Finsupp.degree_single]
    omega
  simp only [evaluation, vector_shift d bound hgrid hbound r j hj, ite_eq_left HV, ite_eq_left HS]
  rw [monomial_add_single, eval₂_mul, eval₂_pow, eval₂_X, pow_one]
  exact mul_comm _ _

theorem evaluation_zero (φ : R →+* L) (bound : ℕ) (x : Fin n → L) :
    evaluation φ bound x (zeroIndex n B) = 1 := by
  simp only [evaluation, vector_zero, map_zero, Nat.zero_le, ite_true, monomial_zero', map_one, eval₂_one]

theorem zero_normal (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) : Normal d (FixedWidthPolynomial.vector n B (zeroIndex n B)) := by
  rw [vector_zero]
  exact hd

end LeanCanny.Algebra.PurePowerReductionMatrix
