/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMatrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Homogeneous common roots annihilate the Macaulay determinant

Evaluating degree-level monomials at a nonzero common homogeneous root gives a
nonzero kernel vector of the padded matrix. Other-degree coordinates are zero,
matching the identity padding rows. This proves determinant vanishing, not a
converse or identification with the multivariate resultant.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open MvPolynomial
open scoped BigOperators Matrix

variable {n : ℕ} {K : Type*} [CommRing K]

theorem eval_fixedWidth (p : MvPolynomial (Fin n) K) (T W : ℕ) (hp : p.totalDegree ≤ T)
    (hW : T < 2 ^ W) (x : Fin n → K) :
    MvPolynomial.eval x p = ∑ r : Index n W, p.coeff (FixedWidthPolynomial.vector n W r) *
      MvPolynomial.eval x (monomial (FixedWidthPolynomial.vector n W r) 1) := by
  have hs := FixedWidthPolynomial.sum_monomials_eq n W p (by
    intro m hm i
    exact ((MvPolynomial.monomial_le_degreeOf i hm).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hp)).trans_lt hW)
  have he := congrArg (MvPolynomial.eval x) hs
  simpa only [map_sum, MvPolynomial.eval_monomial, one_mul] using he.symm

noncomputable def evaluationVector (d : Fin n → ℕ) (W : ℕ) (x : Fin n → K) : Index n W → K :=
  fun r => if (FixedWidthPolynomial.vector n W r).degree = level d then
    MvPolynomial.eval x (monomial (FixedWidthPolynomial.vector n W r) 1) else 0

theorem mulVec_evaluation_eq_zero (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (x : Fin n → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) :
    matrix p d W *ᵥ evaluationVector d W x = 0 := by
  ext r
  change (∑ s, matrix p d W r s * evaluationVector d W x s) = 0
  by_cases hr : (FixedWidthPolynomial.vector n W r).degree = level d
  · have hh := rowPolynomial_homogeneous p d W hp r hr
    calc
      _ = ∑ s : Index n W, (rowPolynomial p d W r hr).coeff (FixedWidthPolynomial.vector n W s) *
          MvPolynomial.eval x (monomial (FixedWidthPolynomial.vector n W s) 1) := by
        apply Finset.sum_congr rfl
        intro s _
        simp only [matrix, dite_eq_left hr, evaluationVector]
        by_cases hs : (FixedWidthPolynomial.vector n W s).degree = level d
        · rw [ite_eq_left hs]
        · rw [ite_eq_right hs, hh.coeff_eq_zero hs]
          simp
      _ = MvPolynomial.eval x (rowPolynomial p d W r hr) := (eval_fixedWidth _ _ W hh.totalDegree_le hW x).symm
      _ = 0 := by
        rw [rowPolynomial, map_mul, hx (pivot d (FixedWidthPolynomial.vector n W r) hr), mul_zero]
  · simp only [matrix, dite_eq_right hr]
    change ((1 : Matrix (Index n W) (Index n W) K) *ᵥ evaluationVector d W x) r = 0
    rw [Matrix.one_mulVec]
    exact ite_eq_right hr

variable [IsDomain K]

theorem evaluationVector_ne_zero (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (x : Fin n → K) (j : Fin n) (hj : x j ≠ 0) : ∃ r : Index n W, evaluationVector d W x r ≠ 0 := by
  have hb : ∀ i : Fin n, (Finsupp.single j (level d)) i < 2 ^ W := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa using hW
    · simp [hi]
  let r := FixedWidthPolynomial.index n W (Finsupp.single j (level d)) hb
  have hv : FixedWidthPolynomial.vector n W r = Finsupp.single j (level d) :=
    FixedWidthPolynomial.vector_index n W _ hb
  have hr : (FixedWidthPolynomial.vector n W r).degree = level d := by rw [hv, Finsupp.degree_single]
  refine ⟨r, ?_⟩
  have he : evaluationVector d W x r = x j ^ level d := by
    rw [evaluationVector, ite_eq_left hr, hv]
    simp [MvPolynomial.eval_monomial]
  rw [he]
  exact pow_ne_zero _ hj

theorem det_eq_zero_of_common_root (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (x : Fin n → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    (matrix p d W).det = 0 := by
  obtain ⟨j, hj⟩ := hnz
  obtain ⟨r, hr⟩ := evaluationVector_ne_zero d W hW x j hj
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (mulVec_evaluation_eq_zero p d W hp hW x hx) (mem_nonZeroDivisors_of_ne_zero hr)

theorem map_det_eq_zero_of_common_root {R : Type*} [CommRing R]
    (φ : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (x : Fin n → K) (hx : ∀ i, MvPolynomial.eval₂ φ x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    φ ((matrix p d W).det) = 0 := by
  rw [φ.map_det]
  change ((matrix p d W).map φ).det = 0
  rw [matrix_map]
  apply det_eq_zero_of_common_root _ d W (fun i => (hp i).map φ) hW x _ hnz
  intro i
  rw [MvPolynomial.eval_map]
  exact hx i

end LeanCanny.Algebra.Macaulay
