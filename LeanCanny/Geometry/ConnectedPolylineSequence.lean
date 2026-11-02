/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ConnectedPolylineTree
public import Mathlib.Topology.ContinuousMap.Compact
/-! # Constructed geometrically convergent ambient polyline approximations

The tree expansions are actually chosen from local connectedness. All original
endpoints are retained. Successive paths are uniformly geometrically close and
every point of the nth path lies within 2⁻ⁿ of the original source.
-/
@[expose] public section
namespace LeanCanny.Geometry.ConnectedPolylineSequence
open Set ConnectedPolylineTree
open scoped Classical unitInterval
variable {X : Type*} [MetricSpace X] [LocallyConnectedSpace X] [PreconnectedSpace X]

noncomputable def scale (n : ℕ) : ℝ := (1/2)^n
theorem scale_pos (n : ℕ) : 0 < scale n := pow_pos (by norm_num) _

theorem exists_trees (a b : X) : ∃ T : ℕ → Tree a b,
    (∀ n, (T n).Fine (scale n)) ∧ ∀ n, (T n).Refines (T (n+1)) := by
  obtain ⟨T₀,_HT,HF⟩ := Tree.exists_inside univ isOpen_univ isPreconnected_univ 1 zero_lt_one ⟨a,mem_univ _⟩ ⟨b,mem_univ _⟩
  choose next HR HB using fun (p : Tree a b) (n : ℕ) => Tree.exists_refinement p (scale (n+1)) (scale_pos _)
  let T : ℕ → Tree a b := Nat.rec T₀ (fun n p => next p n)
  refine ⟨T,?_,?_⟩
  · intro n
    cases n with
    | zero =>
      change T₀.Fine (scale 0)
      simpa only [scale,pow_zero] using HF
    | succ n => exact HB (T n) n
  · intro n
    exact HR (T n) n

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem exists_sequence (e : X → V) (he : Isometry e) (a b : X) :
    ∃ P : ℕ → C(I,V), (∀ n, P n 0=e a ∧ P n 1=e b) ∧
      (∀ n, dist (P n) (P (n+1))≤2*scale n) ∧
      ∀ n t, ∃ x : X, dist (P n t) (e x)≤scale n := by
  obtain ⟨T,HF,HR⟩ := exists_trees a b
  let P : ℕ → C(I,V) := fun n => (realize e (T n)).toContinuousMap
  refine ⟨P,?_,?_,?_⟩
  · intro n
    exact ⟨Path.source _,Path.target _⟩
  · intro n
    apply (ContinuousMap.dist_le (mul_nonneg (by norm_num : (0 : ℝ)≤2) (scale_pos n).le)).mpr
    exact realize_dist_refinement e he (HR n) (scale n) (HF n)
  · intro n t
    exact realize_near_source e he (T n) (scale n) (HF n) t
end LeanCanny.Geometry.ConnectedPolylineSequence
