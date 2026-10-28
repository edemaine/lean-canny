/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PolynomialSystemRegularity
public import LeanCanny.Geometry.RegularPolynomialLevels
public import LeanCanny.Algebra.ProjectionCriticalFamily

/-! # Regular critical systems force their source hypersurface to be regular

A singular hypersurface point satisfies every spatial critical equation.
The base component of the critical-system derivative is then zero, so that
derivative cannot be invertible. Thus an all-critical-roots regularity
certificate also supplies the hypersurface regularity needed for sampling.
-/

@[expose] public section
namespace LeanCanny.Geometry.ProjectionCriticalSourceRegularity
open LeanCanny.Algebra MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_regular (p : MvPolynomial ι ℝ) (base : ι) (v : ι → ℝ)
    (hcritical : ∀ x, (∀ i, (ProjectionCriticalFamily.spatialEquation p base v i).eval x = 0) →
      (fderiv ℝ (fun y => fun i => (ProjectionCriticalFamily.spatialEquation p base v i).eval y) x).IsInvertible)
    (x : ι → ℝ) (hx : p.eval x = 0) :
    Function.Surjective (fderiv ℝ (fun y => p.eval y) x) := by
  apply RegularPolynomialLevels.surjective_of_ne_zero
  intro hz
  have hgrad := (PolynomialCalculus.critical_iff (RingHom.id ℝ) p x).mp hz
  have hzero : ∀ i, (ProjectionCriticalFamily.spatialEquation p base v i).eval x = 0 := by
    intro i
    by_cases hi : i = base
    · simp only [ProjectionCriticalFamily.spatialEquation, ite_eq_left hi, hx]
    · simp only [ProjectionCriticalFamily.spatialEquation, ite_eq_right hi, eval_sub, eval_mul, eval_C,
        show (pderiv i p).eval x = 0 from hgrad i,
        show (pderiv base p).eval x = 0 from hgrad base, mul_zero, sub_self]
  have hD := hcritical x hzero
  have hsys := (PolynomialSystemRegularity.hasFDerivAt (RingHom.id ℝ)
    (ProjectionCriticalFamily.spatialEquation p base v) x).fderiv
  simp only [eval₂_id] at hsys
  rw [hsys] at hD
  obtain ⟨z, hzes⟩ := hD.surjective (fun _ => 1)
  have hb := congrFun hzes base
  change PolynomialCalculus.derivative (RingHom.id ℝ)
    (ProjectionCriticalFamily.spatialEquation p base v base) x z = 1 at hb
  simp only [ProjectionCriticalFamily.spatialEquation, ite_true] at hb
  have hd : PolynomialCalculus.derivative (RingHom.id ℝ) p x = 0 := by
    rw [← PolynomialCalculus.fderiv_eq]
    exact hz
  rw [hd, zero_apply] at hb
  exact zero_ne_one hb

end LeanCanny.Geometry.ProjectionCriticalSourceRegularity
