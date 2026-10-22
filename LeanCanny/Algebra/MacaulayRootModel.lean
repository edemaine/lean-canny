/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayQuotientRoots
public import Mathlib.LinearAlgebra.Matrix.Block

/-! # A homogeneous model preserving a given projective root

For a point with nonzero last coordinate, the forms
`x_last^dᵢ * Xᵢ^dᵢ - xᵢ^dᵢ * X_last^dᵢ` vanish at that point.
Their extraneous matrix is block triangular by the last exponent, with
nonzero diagonal entries. This model supplies a direction for a deformation
that preserves a general root in the last projective chart.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix BigOperators
variable {n : ℕ} {K : Type*} [CommRing K]

noncomputable def rootModel (d : Fin (n + 1) → ℕ) (x : Fin (n + 1) → K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  fun i => MvPolynomial.monomial (Finsupp.single i (d i)) (x (Fin.last n) ^ d i) -
    MvPolynomial.monomial (Finsupp.single (Fin.last n) (d i)) (x i ^ d i)

theorem rootModel_homogeneous (d : Fin (n + 1) → ℕ) (x : Fin (n + 1) → K) (i : Fin (n + 1)) :
    (rootModel d x i).IsHomogeneous (d i) :=
  (MvPolynomial.isHomogeneous_monomial _ (Finsupp.degree_single i (d i))).sub
    (MvPolynomial.isHomogeneous_monomial _ (Finsupp.degree_single (Fin.last n) (d i)))

theorem eval_rootModel (d : Fin (n + 1) → ℕ) (x : Fin (n + 1) → K) (i : Fin (n + 1)) :
    MvPolynomial.eval x (rootModel d x i) = 0 := by
  simp [rootModel, MvPolynomial.eval_monomial, mul_comm]

noncomputable def rootTarget (d : Fin (n + 1) → ℕ) (W : ℕ) (r : extraneousIndices d W) : Fin (n + 1) →₀ ℕ :=
  remainder d (FixedWidthPolynomial.vector (n + 1) W r.val) ((mem_extraneousIndices d W r.val).mp r.property).1 +
    Finsupp.single (Fin.last n)
      (d (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val) ((mem_extraneousIndices d W r.val).mp r.property).1))

theorem rootTarget_last (d : Fin (n + 1) → ℕ) (W : ℕ) (r : extraneousIndices d W) :
    rootTarget d W r (Fin.last n) = FixedWidthPolynomial.vector (n + 1) W r.val (Fin.last n) +
      d (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val) ((mem_extraneousIndices d W r.val).mp r.property).1) := by
  have hr := (mem_extraneousIndices d W r.val).mp r.property
  have hn := pivot_ne_last d _ hr.1 hr.2 (Fin.last n) (fun j => Fin.le_last j)
  simp [rootTarget, remainder, Ne.symm hn]

theorem rowPolynomial_rootModel (d : Fin (n + 1) → ℕ) (W : ℕ) (x : Fin (n + 1) → K)
    (r : Index (n + 1) W) (hr : (FixedWidthPolynomial.vector (n + 1) W r).degree = level d) :
    rowPolynomial (rootModel d x) d W r hr =
      MvPolynomial.monomial (FixedWidthPolynomial.vector (n + 1) W r) (x (Fin.last n) ^ d (pivot d _ hr)) -
        MvPolynomial.monomial (remainder d _ hr + Finsupp.single (Fin.last n) (d (pivot d _ hr)))
          (x (pivot d _ hr) ^ d (pivot d _ hr)) := by
  simp only [rowPolynomial, rootModel, mul_sub, MvPolynomial.monomial_mul_monomial, one_mul, remainder_add]

theorem extraneousMinor_rootModel_apply (d : Fin (n + 1) → ℕ) (W : ℕ) (x : Fin (n + 1) → K)
    (r s : extraneousIndices d W) :
    extraneousMinor (rootModel d x) d W r s =
      (if r = s then x (Fin.last n) ^ d (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val)
        ((mem_extraneousIndices d W r.val).mp r.property).1) else 0) -
      (if rootTarget d W r = FixedWidthPolynomial.vector (n + 1) W s.val then
        x (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val) ((mem_extraneousIndices d W r.val).mp r.property).1) ^
          d (pivot d _ ((mem_extraneousIndices d W r.val).mp r.property).1) else 0) := by
  have hr := (mem_extraneousIndices d W r.val).mp r.property
  change matrix (rootModel d x) d W r.val s.val = _
  rw [matrix, dite_eq_left hr.1, rowPolynomial_rootModel, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_monomial]
  have he : FixedWidthPolynomial.vector (n + 1) W r.val = FixedWidthPolynomial.vector (n + 1) W s.val ↔ r = s :=
    (FixedWidthPolynomial.vector_injective (n + 1) W).eq_iff.trans Subtype.val_injective.eq_iff
  simp only [he, rootTarget]
  rfl

theorem rootTarget_ne_of_last_le (d : Fin (n + 1) → ℕ) (W : ℕ) (hd : ∀ i, 0 < d i)
    (r s : extraneousIndices d W)
    (hs : FixedWidthPolynomial.vector (n + 1) W s.val (Fin.last n) ≤
      FixedWidthPolynomial.vector (n + 1) W r.val (Fin.last n)) :
    rootTarget d W r ≠ FixedWidthPolynomial.vector (n + 1) W s.val := by
  intro he
  have hl := congrArg (fun m : Fin (n + 1) →₀ ℕ => m (Fin.last n)) he
  rw [rootTarget_last] at hl
  have hp := hd (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val)
    ((mem_extraneousIndices d W r.val).mp r.property).1)
  omega

theorem rootModel_blockTriangular (d : Fin (n + 1) → ℕ) (W : ℕ) (hd : ∀ i, 0 < d i) (x : Fin (n + 1) → K) :
    (extraneousMinor (rootModel d x) d W).BlockTriangular
      (fun r => FixedWidthPolynomial.vector (n + 1) W r.val (Fin.last n)) := by
  intro r s hrs
  have hn : r ≠ s := by intro he; subst s; exact lt_irrefl _ hrs
  rw [extraneousMinor_rootModel_apply, ite_eq_right hn,
    ite_eq_right (rootTarget_ne_of_last_le d W hd r s (Nat.le_of_lt hrs)), sub_self]

theorem rootModel_diagonalBlock (d : Fin (n + 1) → ℕ) (W : ℕ) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (k : ℕ) :
    (extraneousMinor (rootModel d x) d W).toSquareBlock
      (fun r => FixedWidthPolynomial.vector (n + 1) W r.val (Fin.last n)) k =
      Matrix.diagonal (fun r : {r : extraneousIndices d W //
          FixedWidthPolynomial.vector (n + 1) W r.val (Fin.last n) = k} =>
        x (Fin.last n) ^ d (pivot d (FixedWidthPolynomial.vector (n + 1) W r.val.val)
        ((mem_extraneousIndices d W r.val.val).mp r.val.property).1)) := by
  funext r s
  change extraneousMinor (rootModel d x) d W r.val s.val = _
  have hs : FixedWidthPolynomial.vector (n + 1) W s.val.val (Fin.last n) ≤
      FixedWidthPolynomial.vector (n + 1) W r.val.val (Fin.last n) := le_of_eq (s.property.trans r.property.symm)
  rw [extraneousMinor_rootModel_apply, ite_eq_right (rootTarget_ne_of_last_le d W hd r.val s.val hs), sub_zero]
  simp only [Matrix.diagonal_apply, Subtype.val_injective.eq_iff]

variable [IsDomain K]

theorem rootModel_extraneous_det_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : x (Fin.last n) ≠ 0) : (extraneousMinor (rootModel d x) d W).det ≠ 0 := by
  rw [(rootModel_blockTriangular d W hd x).det]
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  rw [rootModel_diagonalBlock d W hd x k, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ hx)

end LeanCanny.Algebra.Macaulay
