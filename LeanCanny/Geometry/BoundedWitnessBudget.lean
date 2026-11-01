/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedWeakBooleanWitness
/-! # A polynomial radius budget from the original weak atoms -/
@[expose] public section
namespace LeanCanny.Geometry.BoundedWeakBooleanWitness
open scoped Classical
variable {X I : Type*} [TopologicalSpace X] [Fintype I]
noncomputable def budget (f : I → X → ℝ) (x : X) : ℝ := 1+∑ i, (f i x)^2

omit [TopologicalSpace X] in
theorem budget_nonneg (f : I → X → ℝ) (x : X) : 0≤budget f x := by
  have H : 0≤∑ i, (f i x)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold budget
  linarith

omit [TopologicalSpace X] in
theorem atom_le_budget (f : I → X → ℝ) (x : X) (i : I) : max (f i x) 0≤budget f x := by
  have H := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (f j x)) (Finset.mem_univ i)
  have HN := sq_nonneg (f i x-1/2)
  rw [max_le_iff]
  exact ⟨by dsimp [budget]; nlinarith,budget_nonneg f x⟩

theorem continuous_budget (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) : Continuous (budget f) := by
  exact continuous_const.add (continuous_finsetSum _ (fun i _ => (hf i).pow 2))

end LeanCanny.Geometry.BoundedWeakBooleanWitness
