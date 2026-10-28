/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RetainedParameterPolynomial
public import LeanCanny.Algebra.ParameterSpatialSpecialization
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # Joint parameter and spatial polynomial systems

The first row is the retained univariate parameter equation. The remaining
rows are the spatial system. Its Jacobian determinant is the parameter
derivative times the spatial Jacobian determinant, so a simple parameter root
introduces no new singularity. This includes zero spatial variables.
-/

@[expose] public section
namespace LeanCanny.Algebra.RetainedParameterSystem
open MvPolynomial
open scoped Classical
variable {n : ℕ}

noncomputable def system (p : Polynomial ℤ) (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℤ :=
  Fin.cons (IndexedMultivariateRational.parameter n p) q

theorem zero_iff {K : Type*} [CommRing K] (φ : ℤ →+* K) (p : Polynomial ℤ)
    (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (t : K) (y : Fin n → K) :
    (∀ i, (system p q i).eval₂ φ (Fin.cons t y) = 0) ↔
      p.eval₂ φ t = 0 ∧ ∀ i, (q i).eval₂ φ (Fin.cons t y) = 0 := by
  simp only [system, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    IndexedMultivariateRational.eval_parameter]

theorem jacobian_det {K : Type*} [CommRing K] (φ : ℤ →+* K) (p : Polynomial ℤ)
    (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (t : K) (y : Fin n → K) :
    (Matrix.of (fun i j => (pderiv j (system p q i)).eval₂ φ (Fin.cons t y))).det =
      p.derivative.eval₂ φ t *
        (Matrix.of (fun i j : Fin n => (pderiv j.succ (q i)).eval₂ φ (Fin.cons t y))).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, system, Fin.cons_zero,
    RetainedParameterPolynomial.parameter_partial, RetainedParameterPolynomial.spatial_partial,
    IndexedMultivariateRational.eval_parameter, Fin.val_zero, pow_zero, one_mul,
    eval₂_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  apply congrArg (fun z : K => p.derivative.eval₂ φ t * z)
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.zero_succAbove, Fin.cons_succ]

theorem spatial_det (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (t : ℝ) (y : Fin n → ℝ) :
    (Matrix.of (fun i j : Fin n => (pderiv j.succ (q i)).eval₂ (Int.castRingHom ℝ) (Fin.cons t y))).det =
      (Geometry.PolynomialSystemRegularity.matrix (RingHom.id ℝ)
        (fun i => ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t (q i)) y).det := by
  apply congrArg Matrix.det
  ext i j
  simp only [Geometry.PolynomialSystemRegularity.matrix, Matrix.of_apply]
  rw [← ParameterSpatialSpecialization.specialize_pderiv, eval₂_id, ParameterSpatialSpecialization.eval_specialize]

theorem regular_iff (p : Polynomial ℤ) (q : Fin n → MvPolynomial (Fin (n + 1)) ℤ) (t : ℝ) (y : Fin n → ℝ)
    (ht : p.derivative.eval₂ (Int.castRingHom ℝ) t ≠ 0) :
    (fderiv ℝ (fun z => fun i => (system p q i).eval₂ (Int.castRingHom ℝ) z) (Fin.cons t y)).IsInvertible ↔
      (fderiv ℝ (fun z => fun i =>
        (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t (q i)).eval z) y).IsInvertible := by
  have H := Geometry.PolynomialSystemRegularity.isInvertible_iff (RingHom.id ℝ)
    (fun i => ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t (q i)) y
  simp only [eval₂_id] at H
  rw [Geometry.PolynomialSystemRegularity.isInvertible_iff, H]
  change (Matrix.of (fun i j => (pderiv j (system p q i)).eval₂ (Int.castRingHom ℝ) (Fin.cons t y))).det ≠ 0 ↔ _
  rw [jacobian_det, spatial_det q t y, mul_ne_zero_iff, and_iff_right ht]

end LeanCanny.Algebra.RetainedParameterSystem
