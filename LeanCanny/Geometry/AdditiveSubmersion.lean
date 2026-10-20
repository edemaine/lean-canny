/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialPerturbation
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! # Surjective derivatives for the full additive perturbation family

The derivative of (x,a) ↦ f(x)+a has the right inverse b ↦ (0,b).
Polynomial evaluation and the equation/cube constraint map are smooth, so this
applies to the actual perturbation family. Regularity of fixed-radius slices
remains a separate step.
-/

@[expose] public section

namespace LeanCanny.Geometry.AdditiveSubmersion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def derivative (D : E →L[ℝ] F) : E × F →L[ℝ] F :=
  D.comp (ContinuousLinearMap.fst ℝ E F) + ContinuousLinearMap.snd ℝ E F

theorem hasFDerivAt (f : E → F) (z : E × F) (D : E →L[ℝ] F) (hf : HasFDerivAt f D z.1) :
    HasFDerivAt (fun w : E × F => f w.1 + w.2) (derivative D) z :=
  (hf.comp z hasFDerivAt_fst).add hasFDerivAt_snd

theorem derivative_surjective (D : E →L[ℝ] F) : Function.Surjective (derivative D) := by
  intro b
  exact ⟨(0, b), by simp [derivative]⟩

theorem fderiv_surjective (f : E → F) (z : E × F) (hf : DifferentiableAt ℝ f z.1) :
    Function.Surjective (fderiv ℝ (fun w : E × F => f w.1 + w.2) z) := by
  rw [(hasFDerivAt f z _ hf.hasFDerivAt).fderiv]
  exact derivative_surjective _

end LeanCanny.Geometry.AdditiveSubmersion

namespace LeanCanny.Geometry.PolynomialPerturbation

variable {ι : Type*} [Fintype ι]

theorem contDiff_eval (p : MvPolynomial ι ℤ) :
    ContDiff ℝ ⊤ (fun y : ι → ℝ => p.eval₂ (Int.castRingHom ℝ) y) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C, Int.coe_castRingHom] using (contDiff_const (c := (c : ℝ)))
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (contDiff_apply ℝ ℝ i)

theorem contDiff_value (p : MvPolynomial ι ℤ) (epsilon : ℝ) (i : Constraint ι) : ContDiff ℝ ⊤ (value p epsilon i) := by
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact contDiff_eval p
  · exact (contDiff_eval p).neg
  · exact ((contDiff_apply ℝ ℝ j).add contDiff_const).sub contDiff_const
  · exact (contDiff_const.sub contDiff_const).sub (contDiff_apply ℝ ℝ j)

noncomputable def constraintMap (p : MvPolynomial ι ℤ) (epsilon : ℝ) (y : ι → ℝ) : Constraint ι → ℝ :=
  fun i => value p epsilon i y

noncomputable def parameterMap (p : MvPolynomial ι ℤ) (epsilon : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) : Constraint ι → ℝ := fun i => value p epsilon i z.1 + z.2 i

theorem contDiff_constraintMap (p : MvPolynomial ι ℤ) (epsilon : ℝ) : ContDiff ℝ ⊤ (constraintMap p epsilon) :=
  contDiff_pi.mpr (contDiff_value p epsilon)

theorem contDiff_parameterMap (p : MvPolynomial ι ℤ) (epsilon : ℝ) : ContDiff ℝ ⊤ (parameterMap p epsilon) :=
  ((contDiff_constraintMap p epsilon).comp contDiff_fst).add contDiff_snd

theorem parameterMap_derivative_surjective (p : MvPolynomial ι ℤ) (epsilon : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) : Function.Surjective (fderiv ℝ (parameterMap p epsilon) z) := by
  apply AdditiveSubmersion.fderiv_surjective (constraintMap p epsilon) z
  exact ((contDiff_constraintMap p epsilon).differentiable (by simp)) z.1

end LeanCanny.Geometry.PolynomialPerturbation
