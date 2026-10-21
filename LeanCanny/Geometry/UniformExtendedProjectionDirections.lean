/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformRationalProjectionDirections

/-! # Nearby rational directions with finite fibers in every extension field

One rational direction works for a finite family and a common small positive
real level interval. The exceptional polynomial stays nonzero after every
field extension of the reals, giving finite extended critical fibers there
as well. In particular this covers algebraically closed extensions required
by the characteristic quotient's finite-fiber vanishing theorem.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open Set MvPolynomial
open scoped Topology BigOperators
universe uL
variable {ι : Type*} [Fintype ι]

theorem exists_common_rational_extended_direction_in_extensions {σ : Type*} [Fintype σ]
    (p : σ → MvPolynomial ι ℝ) (base : ι)
    (v : ι → ℝ) (hv : v base = 1) (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ u : Algebra.ProjectionFiniteSpecialization.DirectionIndex base → ℚ,
      rationalDirection base u ∈ U ∧ ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
        ∀ (L : Type uL) [Field L] [Algebra ℝ L], ∀ j,
          {z : Option ι → L | ∀ k, aeval z (Algebra.GenericProjectionFinite.equation
            (Algebra.LevelProjectionSpecialization.levelPolynomial (p j) (algebraMap ℝ L alpha)) base
            (Algebra.ProjectionFiniteSpecialization.normalizedDirection base (fun i => algebraMap ℝ L (u i : ℝ))) k) = 0}.Finite := by
  classical
  choose d hd hfinite using fun j => Algebra.LevelProjectionSpecialization.exists_exceptional_polynomial (p j) base
  have hprod : (∏ j, d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  obtain ⟨u, hu, a, ha, he⟩ := exists_rational_direction_avoiding_levels base v hv U hU (∏ j, d j) hprod
  refine ⟨u, hu, a, ha, ?_⟩
  intro alpha hp hl L _ _ j
  apply hfinite j L (algebraMap ℝ L alpha) (fun i => algebraMap ℝ L (u i : ℝ))
  have hj : MvPolynomial.eval (fun t => t.elim alpha (fun i => (u i : ℝ))) (d j) ≠ 0 := by
    have h := he alpha hp hl
    rw [map_prod] at h
    exact Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
  have hx : (algebraMap ℝ L) ∘ (fun t : Option (Algebra.ProjectionFiniteSpecialization.DirectionIndex base) =>
      t.elim alpha (fun i => (u i : ℝ))) =
      (fun t => t.elim (algebraMap ℝ L alpha) (fun i => algebraMap ℝ L (u i : ℝ))) := by
    funext t
    cases t <;> rfl
  rw [← hx, ← MvPolynomial.eval₂_comp]
  exact (map_ne_zero_iff _ (algebraMap ℝ L).injective).mpr hj
end LeanCanny.Geometry.ProjectionCritical
