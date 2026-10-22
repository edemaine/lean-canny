/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NestedPolynomial
public import LeanCanny.Algebra.ProjectionEquations

/-! # Degree bounds after expanding the projection system's coefficient parameters

Point partial derivatives commute with expansion of the coefficient block.
Taking a partial lowers total degree, while its direction variable adds at
most one. The expanded system therefore has degree at most max(degree(p),1).
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionFlatten
open MvPolynomial
open NestedPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem level (p : MvPolynomial σ (MvPolynomial τ R)) (base : σ) :
    flatten (ProjectionEquations.polynomial p base none) =
      rename (Sum.map Sum.inl id) (flatten p) := flatten_rename Sum.inl p

theorem partial_eq (p : MvPolynomial σ (MvPolynomial τ R)) (base i : σ) :
    flatten (ProjectionEquations.polynomial p base (some i)) =
      rename (Sum.map Sum.inl id) (pderiv (.inl i) (flatten p)) -
        X (.inl (.inr i)) * rename (Sum.map Sum.inl id) (pderiv (.inl base) (flatten p)) := by
  simp only [ProjectionEquations.polynomial, map_sub, map_mul, flatten_rename,
    flatten_X, flatten_pderiv]

theorem degree_le [Nontrivial R] (p : MvPolynomial σ (MvPolynomial τ R)) (base : σ) (j : Option σ) :
    (flatten (ProjectionEquations.polynomial p base j)).totalDegree ≤ max (flatten p).totalDegree 1 := by
  cases j with
  | none => rw [level]; exact (totalDegree_rename_le _ _).trans (le_max_left _ _)
  | some i =>
    rw [partial_eq]
    have hi := PartialDerivativeDegree.degree_le (flatten p) (.inl i)
    have hb := PartialDerivativeDegree.degree_le (flatten p) (.inl base)
    have hri := totalDegree_rename_le (Sum.map (Sum.inl : σ → Sum σ σ) (id : τ → τ)) (pderiv (.inl i) (flatten p))
    have hrb := totalDegree_rename_le (Sum.map (Sum.inl : σ → Sum σ σ) (id : τ → τ)) (pderiv (.inl base) (flatten p))
    have hm := totalDegree_mul
      (X (.inl (.inr i)) : MvPolynomial (Sum (Sum σ σ) τ) R)
      (rename (Sum.map Sum.inl id) (pderiv (.inl base) (flatten p)))
    have hs := totalDegree_sub
      (rename (Sum.map Sum.inl id) (pderiv (.inl i) (flatten p)))
      ((X (.inl (.inr i)) : MvPolynomial (Sum (Sum σ σ) τ) R) *
        rename (Sum.map Sum.inl id) (pderiv (.inl base) (flatten p)))
    simp only [totalDegree_X] at hm
    omega

theorem system_degree_le [Nontrivial R] (p : MvPolynomial σ (MvPolynomial τ R)) (base : σ)
    (j : ProjectionEquations.Index base) :
    (flatten (ProjectionEquations.system p base j)).totalDegree ≤ max (flatten p).totalDegree 1 :=
  degree_le p base _

end LeanCanny.Algebra.ProjectionFlatten
