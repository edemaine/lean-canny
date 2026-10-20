/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # A padded Macaulay coefficient matrix

At degree 1+sum(d_i-1), each monomial is divisible by some coordinate power
X_i^d_i. Choose the first such coordinate and multiply the corresponding input
polynomial by the complementary monomial. Fixed-width ranks enumerate a square
coefficient matrix; ranks of other total degrees receive identity rows.
This defines a determinant candidate, not yet a multivariate resultant.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

def level (d : Fin n → ℕ) : ℕ := (∑ i, (d i - 1)) + 1

theorem level_pos (d : Fin n → ℕ) : 0 < level d := by unfold level; omega

theorem exists_pivot (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    ∃ i, d i ≤ e i := by
  by_contra hn
  have hi (i : Fin n) : e i ≤ d i - 1 := by
    have h : ¬d i ≤ e i := fun h => hn ⟨i, h⟩
    omega
  have hs : e.degree ≤ ∑ i, (d i - 1) := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum (fun i _ => hi i)
  rw [he, level] at hs
  omega

def eligible (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => d i ≤ e i)

theorem eligible_nonempty (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    (eligible d e).Nonempty := by
  obtain ⟨i, hi⟩ := exists_pivot d e he
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

def pivot (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) : Fin n :=
  (eligible d e).min' (eligible_nonempty d e he)

theorem pivot_le (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    d (pivot d e he) ≤ e (pivot d e he) := by
  have hm : pivot d e he ∈ eligible d e := Finset.min'_mem (eligible d e) (eligible_nonempty d e he)
  exact (Finset.mem_filter.mp hm).2

noncomputable def remainder (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) : Fin n →₀ ℕ :=
  e - Finsupp.single (pivot d e he) (d (pivot d e he))

theorem remainder_add (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    remainder d e he + Finsupp.single (pivot d e he) (d (pivot d e he)) = e :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (pivot_le d e he))

theorem remainder_degree (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    (remainder d e he).degree + d (pivot d e he) = level d := by
  have h := congrArg Finsupp.degree (remainder_add d e he)
  simpa only [map_add, Finsupp.degree_single, he] using h

abbrev Index (n W : ℕ) := Fin (FixedWidthPolynomial.count n W)

variable {R : Type*} [CommRing R]

noncomputable def rowPolynomial (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r : Index n W) (hr : (FixedWidthPolynomial.vector n W r).degree = level d) : MvPolynomial (Fin n) R :=
  monomial (remainder d (FixedWidthPolynomial.vector n W r) hr) 1 *
    p (pivot d (FixedWidthPolynomial.vector n W r) hr)

noncomputable def matrix (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    Matrix (Index n W) (Index n W) R := fun r s =>
  if hr : (FixedWidthPolynomial.vector n W r).degree = level d then
    (rowPolynomial p d W r hr).coeff (FixedWidthPolynomial.vector n W s)
  else (1 : Matrix (Index n W) (Index n W) R) r s

theorem rowPolynomial_homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (r : Index n W)
    (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    (rowPolynomial p d W r hr).IsHomogeneous (level d) := by
  have h := (MvPolynomial.isHomogeneous_monomial
    (d := remainder d (FixedWidthPolynomial.vector n W r) hr) (1 : R) rfl).mul
    (hp (pivot d (FixedWidthPolynomial.vector n W r) hr))
  simpa only [rowPolynomial, remainder_degree d _ hr] using h

theorem entry_active (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (r s : Index n W) (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    matrix p d W r s =
      if remainder d (FixedWidthPolynomial.vector n W r) hr ≤ FixedWidthPolynomial.vector n W s then
        (p (pivot d (FixedWidthPolynomial.vector n W r) hr)).coeff
          (FixedWidthPolynomial.vector n W s - remainder d (FixedWidthPolynomial.vector n W r) hr) else 0 := by
  rw [matrix, dite_eq_left hr, rowPolynomial, MvPolynomial.coeff_monomial_mul']
  split_ifs <;> simp

noncomputable def powers (d : Fin n → ℕ) : Fin n → MvPolynomial (Fin n) R :=
  fun i => monomial (Finsupp.single i (d i)) 1

theorem rowPolynomial_powers (d : Fin n → ℕ) (W : ℕ) (r : Index n W)
    (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    rowPolynomial (powers (R := R) d) d W r hr = monomial (FixedWidthPolynomial.vector n W r) 1 := by
  simp only [rowPolynomial, powers, MvPolynomial.monomial_mul_monomial, one_mul, remainder_add]

theorem matrix_powers (d : Fin n → ℕ) (W : ℕ) : matrix (powers (R := R) d) d W = 1 := by
  ext r s
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · rw [matrix, dite_eq_left hr, rowPolynomial_powers]
    simp only [MvPolynomial.coeff_monomial, (FixedWidthPolynomial.vector_injective n W).eq_iff, Matrix.one_apply]
  · simp only [matrix, dite_eq_right hr]

theorem det_matrix_powers (d : Fin n → ℕ) (W : ℕ) : (matrix (powers (R := R) d) d W).det = 1 := by
  rw [matrix_powers, Matrix.det_one]

section Mapping
variable {S : Type*} [CommRing S]

theorem rowPolynomial_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (W : ℕ) (r : Index n W) (hr : (FixedWidthPolynomial.vector n W r).degree = level d) :
    (rowPolynomial p d W r hr).map φ = rowPolynomial (fun i => (p i).map φ) d W r hr := by
  simp only [rowPolynomial, map_mul, MvPolynomial.map_monomial, map_one]

theorem matrix_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (matrix p d W).map φ = matrix (fun i => (p i).map φ) d W := by
  ext r s
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · simp only [Matrix.map_apply, matrix, dite_eq_left hr]
    rw [← rowPolynomial_map φ p d W r hr, MvPolynomial.coeff_map]
  · simp only [Matrix.map_apply, matrix, dite_eq_right hr, Matrix.one_apply]
    by_cases h : r = s <;> simp [h]

end Mapping
end LeanCanny.Algebra.Macaulay
