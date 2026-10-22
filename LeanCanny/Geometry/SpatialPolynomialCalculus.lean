/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialCalculus
public import LeanCanny.Geometry.CriticalEnergyPolynomial
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Spatial critical equations with fixed perturbation parameters

Only spatial coordinates vary when differentiating a radius-slice energy.
Specializing epsilon, delta, and the shifts therefore leaves precisely the
formal partial derivatives in the spatial variable block.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation
open MvPolynomial

variable {ι : Type*} [Fintype ι]

noncomputable def spatialInclusion : (ι → ℝ) →L[ℝ] (Variable ι → ℝ) :=
  ContinuousLinearMap.pi fun v => match v with
    | .inl _ => 0
    | .inr (.inl i) => ContinuousLinearMap.proj i
    | .inr (.inr _) => 0

theorem hasFDerivAt_assignment (epsilon delta : ℝ) (a : Constraint ι → ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => assignment epsilon delta (y, a)) spatialInclusion x := by
  apply hasFDerivAt_pi.mpr
  intro v
  rcases v with b | v
  · cases b <;> simpa [assignment, spatialInclusion] using hasFDerivAt_const (x := x) _
  · rcases v with i | i
    · simpa [assignment, spatialInclusion] using hasFDerivAt_apply (𝕜 := ℝ) i x
    · simpa [assignment, spatialInclusion] using hasFDerivAt_const (x := x) (a i)

theorem spatial_fderiv_eq (q : MvPolynomial (Variable ι) ℤ) (epsilon delta : ℝ)
    (a : Constraint ι → ℝ) (x : ι → ℝ) :
    fderiv ℝ (fun y => q.eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (y, a))) x =
      (PolynomialCalculus.derivative (Int.castRingHom ℝ) q (assignment epsilon delta (x, a))).comp
        spatialInclusion := by
  exact ((PolynomialCalculus.hasFDerivAt _ q _).comp x (hasFDerivAt_assignment epsilon delta a x)).fderiv

variable [DecidableEq ι]

omit [Fintype ι] in
theorem spatialInclusion_single (i : ι) :
    spatialInclusion (Pi.single i 1) = Pi.single (.inr (.inl i) : Variable ι) 1 := by
  classical
  ext v
  rcases v with b | v
  · simp [spatialInclusion]
  · rcases v with j | j <;> simp [spatialInclusion, Pi.single_apply]

theorem spatial_fderiv_single (q : MvPolynomial (Variable ι) ℤ) (epsilon delta : ℝ)
    (a : Constraint ι → ℝ) (x : ι → ℝ) (i : ι) :
    fderiv ℝ (fun y => q.eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (y, a))) x (Pi.single i 1) =
      (pderiv (.inr (.inl i)) q).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (x, a)) := by
  rw [spatial_fderiv_eq, ContinuousLinearMap.comp_apply, spatialInclusion_single]
  exact PolynomialCalculus.derivative_single _ _ _ _

theorem spatial_critical_iff (q : MvPolynomial (Variable ι) ℤ) (epsilon delta : ℝ)
    (a : Constraint ι → ℝ) (x : ι → ℝ) :
    fderiv ℝ (fun y => q.eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (y, a))) x = 0 ↔
      ∀ i : ι, (pderiv (.inr (.inl i)) q).eval₂ (Int.castRingHom ℝ) (assignment epsilon delta (x, a)) = 0 := by
  rw [PolynomialCalculus.linear_eq_zero_iff]
  simp only [spatial_fderiv_single]

theorem energy_critical_iff (p : MvPolynomial ι ℤ) (s : Finset (Constraint ι)) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) :
    fderiv ℝ (ActiveRadius.energy (constraintMap p epsilon) s) z.1 = 0 ↔
      ∀ i : ι, (pderiv (.inr (.inl i)) (energyPolynomial p s)).eval₂ (Int.castRingHom ℝ)
        (assignment epsilon delta z) = 0 := by
  simpa only [eval_energyPolynomial] using spatial_critical_iff (energyPolynomial p s) epsilon delta z.2 z.1

end LeanCanny.Geometry.PolynomialPerturbation
