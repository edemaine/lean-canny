/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ProjectionCritical
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Strict normalized supporting projections of compact sets

A farthest point from a center strictly maximizes the projection in the
direction from the center to that point. Choosing the center below the whole
compact set in one coordinate makes that direction's coordinate positive,
so it can be normalized to one without changing the strict maximum.
-/

@[expose] public section

namespace LeanCanny.Geometry.CompactSupportingProjection
open Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def squaredDistance (a x : ι → ℝ) : ℝ := ∑ i, (x i - a i) ^ 2

theorem continuous_squaredDistance (a : ι → ℝ) : Continuous (squaredDistance a) :=
  continuous_finsetSum _ (fun i _ => ((continuous_apply i).sub continuous_const).pow 2)

theorem projection_apply (v x : ι → ℝ) : ProjectionCritical.projection v x = ∑ i, v i * x i := by
  simp [ProjectionCritical.projection]

theorem squaredDistance_identity (a p x : ι → ℝ) :
    squaredDistance a x - squaredDistance a p =
      2 * (ProjectionCritical.projection (fun i => p i - a i) x -
        ProjectionCritical.projection (fun i => p i - a i) p) + squaredDistance p x := by
  simp only [squaredDistance, projection_apply, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem squaredDistance_pos (p x : ι → ℝ) (hne : x ≠ p) : 0 < squaredDistance p x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j - p j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩

theorem strict_projection_of_farthest (K : Set (ι → ℝ)) (a p : ι → ℝ)
    (hmax : IsMaxOn (squaredDistance a) K p) :
    ∀ x ∈ K, x ≠ p → ProjectionCritical.projection (fun i => p i - a i) x <
      ProjectionCritical.projection (fun i => p i - a i) p := by
  intro x hx hne
  have hb : squaredDistance a x ≤ squaredDistance a p := hmax hx
  have hid := squaredDistance_identity a p x
  have hp := squaredDistance_pos p x hne
  linarith

theorem projection_mul (c : ℝ) (v x : ι → ℝ) :
    ProjectionCritical.projection (fun i => c * v i) x = c * ProjectionCritical.projection v x := by
  simp only [projection_apply, Finset.mul_sum, mul_assoc]

theorem exists_strict_normalized (K : Set (ι → ℝ)) (hK : IsCompact K) (hn : K.Nonempty) (base : ι) :
    ∃ (v p : ι → ℝ), p ∈ K ∧ v base = 1 ∧
      ∀ x ∈ K, x ≠ p → ProjectionCritical.projection v x < ProjectionCritical.projection v p := by
  classical
  obtain ⟨m, _, hm⟩ := hK.exists_isMinOn hn (continuous_apply base).continuousOn
  let a : ι → ℝ := Function.update (fun _ => 0) base (m base - 1)
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hn (continuous_squaredDistance a).continuousOn
  let c := p base - a base
  have hc : 0 < c := by
    have hbound : m base ≤ p base := hm hp
    dsimp [c, a]
    simp only [Function.update_self]
    linarith
  let v : ι → ℝ := fun i => c⁻¹ * (p i - a i)
  refine ⟨v, p, hp, ?_, ?_⟩
  · exact inv_mul_cancel₀ hc.ne'
  · intro x hx hne
    have hstrict := strict_projection_of_farthest K a p hmax x hx hne
    change ProjectionCritical.projection (fun i => c⁻¹ * (p i - a i)) x <
      ProjectionCritical.projection (fun i => c⁻¹ * (p i - a i)) p
    rw [projection_mul, projection_mul]
    exact mul_lt_mul_of_pos_left hstrict (inv_pos.mpr hc)

end LeanCanny.Geometry.CompactSupportingProjection
