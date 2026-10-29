/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineCriticalExtremum

/-! # Nonsingular affine critical stages lie on regular slices

The source and active old-height derivatives are selected rows of the full
spatial Jacobian and have no multiplier terms. Solving the full invertible
matrix and retaining its ambient coordinates proves constraint surjectivity.
No root assumption is needed for this implication.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSliceRegularity
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalStage FlatAffineCriticalRegularity
open FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem surjective (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → ℝ)
    (hdet : (matrix φ p s a b z).det ≠ 0) :
    Function.Surjective (derivative φ p s a (z ∘ ambient)) := by
  have hM : Function.Surjective (matrix φ p s a b z).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro r
  let target : Variables n → ℝ := Sum.elim (fun _ => 0)
    (Fin.cases (r none) (fun j => if hj : j ∈ s then r (some ⟨j, hj⟩) else 0))
  obtain ⟨d, hd⟩ := hM target
  refine ⟨fun i => d (Sum.inl i), ?_⟩
  funext j
  cases j with
  | none =>
    have h := congrFun hd (Sum.inr 0)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix_source_ambient,
      matrix_source_multiplier, zero_mul, Finset.sum_const_zero, add_zero, target,
      Sum.elim_inr, Fin.cases_zero] at h
    simpa only [derivative, ContinuousLinearMap.pi_apply, constraint,
      PolynomialCalculus.derivative_apply] using h
  | some j =>
    have h := congrFun hd (Sum.inr j.val.succ)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix_level_ambient,
      matrix_level_multiplier, j.property, ite_true, zero_mul, Finset.sum_const_zero,
      add_zero, target, Sum.elim_inr, Fin.cases_succ, dite_true] at h
    simpa only [derivative, ContinuousLinearMap.pi_apply, constraint,
      PolynomialCalculus.derivative_apply, height_partial] using h

theorem active_card_lt (φ : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (z : (ι ⊕ Variables n) → ℝ)
    (hdet : (matrix φ p s a b z).det ≠ 0) : s.card < n := by
  have H := LinearMap.finrank_le_finrank_of_surjective
    (f := (derivative φ p s a (z ∘ ambient)).toLinearMap) (surjective φ p s a b z hdet)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe, Fintype.card_fin] at H
  omega

end LeanCanny.Geometry.FlatAffineSliceRegularity
