/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCriticalFamily
public import LeanCanny.Geometry.PolynomialSystemRegularity

/-! # Critical systems under a nonzero constant scaling

Clearing denominators that depend only on frozen coordinates multiplies a
slice polynomial by a constant. Its critical equations acquire the same
factor. All roots and their analytic regularity are preserved, without any
assumption that the critical set is finite or regular.
-/

@[expose] public section
namespace LeanCanny.Geometry.ScaledCriticalSystem
open MvPolynomial LeanCanny.Algebra
open scoped Classical
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

theorem equation (q : MvPolynomial ι R) (b : ι) (v : ι → R) (c : R) (i : ι) :
    ProjectionCriticalFamily.spatialEquation (C c * q) b v i =
      C c * ProjectionCriticalFamily.spatialEquation q b v i := by
  by_cases hi : i = b
  · simp only [ProjectionCriticalFamily.spatialEquation, hi, ite_true]
  · simp only [ProjectionCriticalFamily.spatialEquation, hi, ite_false, pderiv_C_mul]
    ring

theorem zero_iff {K : Type*} [Field K] (φ : R →+* K) (q : MvPolynomial ι R)
    (b : ι) (v : ι → R) (c : R) (hc : φ c ≠ 0) (x : ι → K) :
    (∀ i, (ProjectionCriticalFamily.spatialEquation (C c * q) b v i).eval₂ φ x = 0) ↔
      ∀ i, (ProjectionCriticalFamily.spatialEquation q b v i).eval₂ φ x = 0 := by
  simp only [equation, eval₂_mul, eval₂_C, mul_eq_zero, hc, false_or]

theorem matrix [Fintype ι] (φ : R →+* ℝ) (q : MvPolynomial ι R)
    (b : ι) (v : ι → R) (c : R) (x : ι → ℝ) :
    PolynomialSystemRegularity.matrix φ (ProjectionCriticalFamily.spatialEquation (C c * q) b v) x =
      φ c • PolynomialSystemRegularity.matrix φ (ProjectionCriticalFamily.spatialEquation q b v) x := by
  ext i j
  simp only [PolynomialSystemRegularity.matrix, Matrix.of_apply, equation, pderiv_C_mul,
    eval₂_mul, eval₂_C, Matrix.smul_apply, smul_eq_mul]

theorem determinant [Fintype ι] (φ : R →+* ℝ) (q : MvPolynomial ι R)
    (b : ι) (v : ι → R) (c : R) (x : ι → ℝ) :
    (PolynomialSystemRegularity.matrix φ (ProjectionCriticalFamily.spatialEquation (C c * q) b v) x).det =
      φ c ^ Fintype.card ι *
        (PolynomialSystemRegularity.matrix φ (ProjectionCriticalFamily.spatialEquation q b v) x).det := by
  rw [matrix, Matrix.det_smul]

theorem regular_iff [Fintype ι] (φ : R →+* ℝ) (q : MvPolynomial ι R)
    (b : ι) (v : ι → R) (c : R) (hc : φ c ≠ 0) (x : ι → ℝ) :
    (fderiv ℝ (fun y => fun i =>
      (ProjectionCriticalFamily.spatialEquation (C c * q) b v i).eval₂ φ y) x).IsInvertible ↔
      (fderiv ℝ (fun y => fun i =>
        (ProjectionCriticalFamily.spatialEquation q b v i).eval₂ φ y) x).IsInvertible := by
  rw [PolynomialSystemRegularity.isInvertible_iff, PolynomialSystemRegularity.isInvertible_iff,
    determinant, mul_ne_zero_iff, and_iff_right (pow_ne_zero _ hc)]

omit [DecidableEq ι] in
theorem hypersurface_regular_iff [Fintype ι] (φ : R →+* ℝ) (q : MvPolynomial ι R)
    (c : R) (hc : φ c ≠ 0) (x : ι → ℝ) :
    Function.Surjective (fderiv ℝ (fun y => (C c * q).eval₂ φ y) x) ↔
      Function.Surjective (fderiv ℝ (fun y => q.eval₂ φ y) x) := by
  have he : (fun y => (C c * q).eval₂ φ y) = (fun y => φ c * q.eval₂ φ y) := by
    funext y
    rw [eval₂_mul, eval₂_C]
  rw [he, fderiv_const_mul (PolynomialCalculus.hasFDerivAt φ q x).differentiableAt]
  constructor
  · intro h z
    obtain ⟨y, hy⟩ := h (φ c * z)
    exact ⟨y, mul_left_cancel₀ hc (by simpa only [smul_apply, smul_eq_mul] using hy)⟩
  · intro h z
    obtain ⟨y, hy⟩ := h ((φ c)⁻¹ * z)
    refine ⟨y, ?_⟩
    simp only [smul_apply, smul_eq_mul, hy, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end LeanCanny.Geometry.ScaledCriticalSystem
