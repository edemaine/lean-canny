/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerDifference
public import LeanCanny.CountingHierarchy.DeterminantTopDegree
public import LeanCanny.CountingHierarchy.PurePowerResidue
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # A divided-difference matrix for pure-power relations -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial
open scoped Classical BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The lower parts determine a divided-difference matrix. Its highest
 degree part is diagonal and its diagonal evaluation is the Jacobian. -/
theorem purePower_difference_matrix (x : Fin n → A) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) A) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hx : ∀ i, eval x (r i) = x i ^ (d + 1)) :
    ∃ W : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A),
      (∀ i, ∑ j, W i j * (C (x j) - X j) = -(X i ^ (d + 1) - r i)) ∧
      (∀ i j, (W i j).totalDegree ≤ d) ∧
      (∀ i j, (W i j - Matrix.diagonal (fun j => X j ^ d) i j).totalDegree < d) ∧
      (∀ i j, eval x (W i j) = eval x (pderiv j (X i ^ (d + 1) - r i))) := by
  have hr' (i : Fin n) : (r i).totalDegree ≤ (d - 1) + 1 := by have := hr i; omega
  choose D hdiff hdegree hdiag using
    (fun i => polynomial_divided_differences x (r i) (d - 1) (hr' i))
  let W : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A) := fun i j =>
    (if i = j then purePowerDifference (x i) i d else 0) - D i j
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [W, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [purePowerDifference_mul, ← hdiff i, hx i]
    ring
  · intro i j
    have hD := hdegree i j
    have hg : (if i = j then purePowerDifference (x i) i d else
        (0 : MvPolynomial (Fin n) A)).totalDegree ≤ d := by
      split_ifs
      · exact purePowerDifference_degree _ _ _
      · simp
    exact (totalDegree_sub _ _).trans (max_le hg (by omega))
  · intro i j
    have hD := hdegree i j
    by_cases hij : i = j
    · subst j
      have heq : W i i - Matrix.diagonal (fun j => X j ^ d) i i =
          (purePowerDifference (x i) i d - X i ^ d) - D i i := by
        simp only [W, ↓reduceIte, Matrix.diagonal_apply_eq]
        ring
      rw [heq]
      apply (totalDegree_sub _ _).trans_lt
      exact max_lt_iff.mpr ⟨purePowerDifference_lower_degree _ _ hd, by omega⟩
    · simp only [W, hij, ↓reduceIte, zero_sub, Matrix.diagonal_apply_ne _ hij,
        sub_zero, totalDegree_neg]
      omega
  · intro i j
    simp only [W, map_sub, hdiag, pderiv_pow, pderiv_X, Pi.single_apply,
      map_mul, map_natCast, map_pow, eval_X]
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, purePowerDifference_diagonal, Nat.add_sub_cancel,
        mul_one, map_one]
    · simp [hij]

end LeanCanny.CountingHierarchy
