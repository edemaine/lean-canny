/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCriticalHomogenization

/-! # Finite affine charts for testing projective root-freeness

Every nonzero homogeneous common root can be rescaled to have one coordinate
equal to one. Thus the projective test is exactly emptiness of the finitely
many normalized affine root systems.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveRootCharts
open MvPolynomial
open scoped Classical

variable {σ κ R K : Type*} [CommRing R] [Field K]

theorem root_free_iff_charts (p : κ → MvPolynomial σ R) (d : κ → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (d j)) (φ : R →+* K) :
    (∀ x : σ → K, (∀ j, (p j).eval₂ φ x = 0) → x = 0) ↔
      ∀ i : σ, ¬ ∃ x : σ → K, x i = 1 ∧ ∀ j, (p j).eval₂ φ x = 0 := by
  constructor
  · intro h i ⟨x, hi, hx⟩
    have he := congrFun (h x hx) i
    rw [hi, Pi.zero_apply] at he
    exact one_ne_zero he
  · intro h x hx
    funext i
    by_contra hi
    have hxi : x i ≠ 0 := hi
    let y : σ → K := fun j => (x i)⁻¹ * x j
    apply h i
    refine ⟨y, inv_mul_cancel₀ hxi, ?_⟩
    intro j
    rw [← eval_map]
    change eval (fun j => (x i)⁻¹ * x j) ((p j).map φ) = 0
    rw [CoerciveCriticalHomogenization.eval_scale _ _ ((hp j).map φ), eval_map, hx j, mul_zero]

end LeanCanny.Algebra.ProjectiveRootCharts
