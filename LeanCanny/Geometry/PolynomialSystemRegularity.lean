/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialCalculus
public import LeanCanny.Algebra.JacobianKernelCharts
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Analytic regularity of square polynomial systems

The evaluated formal Jacobian is the derivative of the actual polynomial
system. Its determinant is nonzero exactly when that derivative is invertible,
including for a system in zero variables.
-/

@[expose] public section
namespace LeanCanny.Geometry.PolynomialSystemRegularity
open MvPolynomial LeanCanny.Algebra
open scoped Classical

variable {ι R : Type*} [Fintype ι] [CommRing R]

noncomputable def derivative (φ : R →+* ℝ) (q : ι → MvPolynomial ι R) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => PolynomialCalculus.derivative φ (q i) x)

theorem hasFDerivAt (φ : R →+* ℝ) (q : ι → MvPolynomial ι R) (x : ι → ℝ) :
    HasFDerivAt (fun y => fun i => (q i).eval₂ φ y) (derivative φ q x) x :=
  hasFDerivAt_pi.mpr (fun i => PolynomialCalculus.hasFDerivAt φ (q i) x)

theorem derivative_apply (φ : R →+* ℝ) (q : ι → MvPolynomial ι R) (x h : ι → ℝ) :
    derivative φ q x h = Matrix.mulVec (fun i j => (pderiv j (q i)).eval₂ φ x) h := by
  funext i
  exact PolynomialCalculus.derivative_apply φ (q i) x h

variable [DecidableEq ι]

noncomputable def matrix (φ : R →+* ℝ) (q : ι → MvPolynomial ι R) (x : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of (fun i j => (pderiv j (q i)).eval₂ φ x)

theorem isInvertible_iff (φ : R →+* ℝ) (q : ι → MvPolynomial ι R) (x : ι → ℝ) :
    (fderiv ℝ (fun y => fun i => (q i).eval₂ φ y) x).IsInvertible ↔
      (matrix φ q x).det ≠ 0 := by
  rw [(hasFDerivAt φ q x).fderiv]
  let M := matrix φ q x
  have hD : ∀ h, derivative φ q x h = M.mulVec h := derivative_apply φ q x
  constructor
  · intro h
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det M).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro a b hab
    apply h.injective
    simpa only [hD] using hab
  · intro hdet
    have hinj : Function.Injective (derivative φ q x) := by
      intro a b hab
      apply Matrix.mulVec_injective_of_det_ne_zero hdet
      simpa only [hD] using hab
    refine ⟨(LinearEquiv.ofInjectiveOfFinrankEq (derivative φ q x).toLinearMap hinj rfl).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.coe_injective
    exact LinearEquiv.coe_ofInjectiveOfFinrankEq _ hinj rfl

end LeanCanny.Geometry.PolynomialSystemRegularity
