/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.Compact
/-! # Compact polynomial squared-distance fibers in the original coordinate tuple -/
@[expose] public section
namespace LeanCanny.Geometry.SquaredDistanceFibers
open Set Metric
open scoped BigOperators
variable {n : ℕ}

def value (center x : Fin n → ℝ) : ℝ := ∑ i, (x i-center i)^2

theorem nonneg (center x : Fin n → ℝ) : 0≤value center x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_value (center : Fin n → ℝ) : Continuous (value center) :=
  continuous_finsetSum _ (fun i _ => ((continuous_apply i).sub continuous_const).pow 2)

theorem norm_sq (center x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))-WithLp.toLp 2 center‖^2=value center x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem compact_level (center : Fin n → ℝ) (r : ℝ) (hr : 0≤r) :
    IsCompact {x : Fin n → ℝ | value center x=r} := by
  let E := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
  have HE : {x : Fin n → ℝ | value center x=r}=E ⁻¹' sphere (E center) (Real.sqrt r) := by
    ext x
    change value center x=r ↔ ‖E x-E center‖=Real.sqrt r
    have HN : ‖E x-E center‖^2=value center x := norm_sq center x
    constructor
    · intro H
      rw [← HN] at H
      have HS := Real.sqrt_sq (norm_nonneg (E x-E center))
      rw [H] at HS
      exact HS.symm
    · intro H
      rw [← HN,H,Real.sq_sqrt hr]
  rw [HE]
  exact E.isCompact_preimage.mpr (isCompact_sphere _ _)

theorem zero_iff (center x : Fin n → ℝ) : value center x=0 ↔ x=center := by
  rw [← norm_sq]
  constructor
  · intro H
    have HN : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))-WithLp.toLp 2 center‖=0 := by
      nlinarith [norm_nonneg ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))-WithLp.toLp 2 center)]
    exact WithLp.toLp_injective 2 (sub_eq_zero.mp (norm_eq_zero.mp HN))
  · rintro rfl
    simp

end LeanCanny.Geometry.SquaredDistanceFibers
