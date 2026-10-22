/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Exact feasibility from arbitrarily accurate compact approximations

The sum of the negative parts of finitely many continuous constraints attains
a minimum on a compact set. Uniformly arbitrarily small violations force that
minimum to be zero. This supplies the compactness direction of perturbation
correctness without assuming a convergent choice of approximate solutions.
-/

@[expose] public section

namespace LeanCanny.Geometry.CompactApproximation
open scoped BigOperators

variable {X I : Type*} [TopologicalSpace X] [Fintype I]

noncomputable def violation (f : I → X → ℝ) (x : X) : ℝ := ∑ i, max 0 (-f i x)

omit [TopologicalSpace X] in
theorem violation_nonneg (f : I → X → ℝ) (x : X) : 0 ≤ violation f x :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

omit [TopologicalSpace X] in
theorem violation_eq_zero_iff (f : I → X → ℝ) (x : X) : violation f x = 0 ↔ ∀ i, 0 ≤ f i x := by
  classical
  constructor
  · intro h i
    have hi : max 0 (-f i x) ≤ violation f x :=
      Finset.single_le_sum (f := fun j => max 0 (-f j x)) (fun _ _ => le_max_left _ _) (Finset.mem_univ i)
    have := (le_max_right 0 (-f i x)).trans hi
    rw [h] at this
    linarith
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    exact max_eq_left (by linarith [h i])

theorem continuous_violation (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) : Continuous (violation f) :=
  continuous_finsetSum Finset.univ fun i _ => continuous_const.max (hf i).neg

omit [TopologicalSpace X] in
theorem violation_le (f : I → X → ℝ) (x : X) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hf : ∀ i, -epsilon ≤ f i x) : violation f x ≤ (Fintype.card I : ℝ) * epsilon := by
  calc
    _ ≤ ∑ _i : I, epsilon := Finset.sum_le_sum fun i _ => max_le he (by linarith [hf i])
    _ = _ := by simp

theorem exists_feasible (K : Set X) (hK : IsCompact K) (f : I → X → ℝ) (hf : ∀ i, Continuous (f i))
    (ha : ∀ epsilon : ℝ, 0 < epsilon → ∃ x ∈ K, ∀ i, -epsilon ≤ f i x) :
    ∃ x ∈ K, ∀ i, 0 ≤ f i x := by
  obtain ⟨x, hx, _⟩ := ha 1 (by norm_num)
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ (continuous_violation f hf).continuousOn
  refine ⟨y, hy, (violation_eq_zero_iff f y).mp ?_⟩
  apply le_antisymm _ (violation_nonneg f y)
  by_contra h
  have hv : 0 < violation f y := lt_of_not_ge h
  let m : ℝ := Fintype.card I
  have hm : 0 < m + 1 := by dsimp [m]; positivity
  let epsilon := violation f y / (m + 1)
  have he : 0 < epsilon := div_pos hv hm
  obtain ⟨z, hz, hzf⟩ := ha epsilon he
  have hbound := (hmin hz).trans (violation_le f z epsilon he.le hzf)
  have hid : epsilon * (m + 1) = violation f y := div_mul_cancel₀ _ (ne_of_gt hm)
  change violation f y ≤ m * epsilon at hbound
  nlinarith

theorem exists_feasible_iff (K : Set X) (hK : IsCompact K) (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∃ x ∈ K, ∀ i, 0 ≤ f i x) ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ x ∈ K, ∀ i, -epsilon ≤ f i x := by
  constructor
  · rintro ⟨x, hx, hxf⟩ epsilon he
    exact ⟨x, hx, fun i => (by linarith : -epsilon ≤ 0).trans (hxf i)⟩
  · exact exists_feasible K hK f hf

end LeanCanny.Geometry.CompactApproximation
