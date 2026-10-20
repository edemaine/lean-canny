/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformRationalProjectionDirections
public import LeanCanny.Geometry.TubeCriticalSampling
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # A fixed rational finite-root direction throughout a tube interval

Every neighborhood of a normalized direction contains one rational direction
whose root sets are finite for all active sets at every sufficiently small
positive tube level. The direction is independent of that level.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set MvPolynomial
open scoped Topology

variable {ι : Type*} [Fintype ι]

theorem level_realEnergy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) :
    Algebra.LevelProjectionSpecialization.levelPolynomial (realEnergy p s epsilon delta) alpha =
      (polynomial p s).map (coefficientMap epsilon delta alpha) := by
  apply MvPolynomial.funext
  intro x
  simp only [Algebra.LevelProjectionSpecialization.levelPolynomial, eval_sub, eval_C, eval_map,
    Algebra.algebraMap_self, eval₂_id]
  exact (eval_as_realEnergy p s epsilon delta alpha x).symm

theorem exists_uniform_rational_finite_direction_near (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (hv : v (base ι) = 1)
    (U : Set (Coordinate ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex (base ι) → ℚ,
      ProjectionCritical.rationalDirection (base ι) u ∈ U ∧ ∃ a : ℝ, 0 < a ∧
        ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ s : Finset (PolynomialPerturbation.Constraint ι),
          (projectionRootSet p s epsilon delta alpha (ProjectionCritical.rationalDirection (base ι) u)).Finite := by
  classical
  have hregular : ∃ b : ℝ, 0 < b ∧ ∀ alpha : ℝ, 0 < alpha → alpha < b →
      ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (x : Coordinate ι → ℝ),
        (realEnergy p s epsilon delta).eval₂ (RingHom.id ℝ) x = alpha →
          Function.Surjective (fderiv ℝ (fun y => (realEnergy p s epsilon delta).eval₂ (RingHom.id ℝ) y) x) := by
    obtain ⟨b, hb, hr⟩ := exists_common_regular_interval p epsilon delta
    refine ⟨b, hb, ?_⟩
    intro alpha hp hl s x hx
    have he : (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 := by
      rw [eval_as_realEnergy]
      exact sub_eq_zero.mpr hx
    have h := hr alpha hp hl s x he
    simp_rw [eval_as_realEnergy] at h
    rw [fderiv_sub_const] at h
    exact h
  obtain ⟨u, hu, a, ha, hf⟩ := ProjectionCritical.exists_common_rational_direction_interval_near
    (fun s => realEnergy p s epsilon delta) (base ι) hregular v hv U hU
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl s
  have h := hf alpha hp hl s
  rw [level_realEnergy] at h
  apply h.subset
  intro x hx j
  rw [ProjectionCritical.system_eval_map]
  have he := hx j
  rw [eval_integerProjection] at he
  exact he

end LeanCanny.Geometry.TubePolynomial
