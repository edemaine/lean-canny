/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RadiusLinearization

/-! # The squared-radius derivative and the actual joint constraint map

Its derivative is twice the dot product with the shift vector. The free-radius
joint map has surjective derivative at every nonzero radius parameter. The
fixed-radius derivative has an explicit weighted spatial-derivative criterion.
-/

@[expose] public section

namespace LeanCanny.Geometry.SquaredRadius
open scoped BigOperators

variable {I : Type*} [Fintype I]

noncomputable def value (a : I → ℝ) : ℝ := ∑ i, a i ^ 2

noncomputable def derivative (a : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2 * a i) • ContinuousLinearMap.proj i

theorem derivative_apply (a b : I → ℝ) : derivative a b = 2 * ∑ i, a i * b i := by
  simp [derivative, Finset.mul_sum, mul_assoc]

theorem hasFDerivAt (a : I → ℝ) : HasFDerivAt value (derivative a) a := by
  unfold value derivative
  apply HasFDerivAt.fun_sum
  intro i _
  simpa only [show 2 - 1 = 1 from rfl, pow_one, two_nsmul, two_mul] using
    (hasFDerivAt_apply (𝕜 := ℝ) i a).pow 2

theorem contDiff : ContDiff ℝ ⊤ (value (I := I)) :=
  ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ i).pow 2)

theorem differentiable : Differentiable ℝ (value (I := I)) := contDiff.differentiable (by simp)

theorem fderiv_eq (a : I → ℝ) : fderiv ℝ value a = derivative a := (hasFDerivAt a).fderiv

end LeanCanny.Geometry.SquaredRadius

namespace LeanCanny.Geometry.PolynomialPerturbation
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def fixedConstraintMap (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    (ι → ℝ) × (Constraint ι → ℝ) → (Constraint ι → ℝ) × ℝ :=
  RadiusLinearization.fixedMap (constraintMap p epsilon) SquaredRadius.value delta

noncomputable def jointConstraintMap (p : MvPolynomial ι ℤ) (epsilon : ℝ) :
    ((ι → ℝ) × (Constraint ι → ℝ)) × ℝ → (Constraint ι → ℝ) × ℝ :=
  RadiusLinearization.jointMap (constraintMap p epsilon) SquaredRadius.value

theorem jointConstraintMap_derivative_surjective (p : MvPolynomial ι ℤ) (epsilon : ℝ)
    (z : ((ι → ℝ) × (Constraint ι → ℝ)) × ℝ) (hd : z.2 ≠ 0) :
    Function.Surjective (fderiv ℝ (jointConstraintMap p epsilon) z) :=
  RadiusLinearization.jointMap_fderiv_surjective _ _ z
    (((contDiff_constraintMap p epsilon).differentiable (by simp)) z.1.1)
    (SquaredRadius.differentiable z.1.2) hd

theorem fixedConstraintMap_derivative_criterion (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    Function.Surjective (fderiv ℝ (fixedConstraintMap p epsilon delta) z) ↔
      (SquaredRadius.derivative z.2).comp (fderiv ℝ (constraintMap p epsilon) z.1) ≠ 0 := by
  unfold fixedConstraintMap
  rw [RadiusLinearization.fixedMap_fderiv_surjective_iff _ _ delta z
    (((contDiff_constraintMap p epsilon).differentiable (by simp)) z.1) (SquaredRadius.differentiable z.2),
    SquaredRadius.fderiv_eq]

end LeanCanny.Geometry.PolynomialPerturbation
