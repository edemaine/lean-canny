/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IndependentRealDirections
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith

/-! # Generic normalized directions in every neighborhood

Keep one direction coordinate equal to one and choose the remaining
coordinates independently in a small product of intervals. Thus normalized
directions independent over a countable real coefficient field can approximate
every normalized real direction.
-/

@[expose] public section

namespace LeanCanny.Geometry.IndependentRealDirections
open Set
open scoped Topology

variable {K ι : Type*} [Field K] [Algebra K ℝ] [Countable K] [Fintype ι]

theorem exists_normalized_near (base : ι) (v : ι → ℝ) (hv : v base = 1)
    (U : Set (ι → ℝ)) (hU : U ∈ nhds v) :
    ∃ w ∈ U, w base = 1 ∧ AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => w i) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨u, hu, hb⟩ := exists_in_intervals (K := K) {i : ι // i ≠ base}
    (fun i => v i - r) (fun i => v i + r) (fun i => by linarith)
  let w : ι → ℝ := fun i => if hi : i = base then 1 else u ⟨i, hi⟩
  have hw : w base = 1 := by simp [w]
  have hdist : ∀ i, dist (w i) (v i) < r := by
    intro i
    by_cases hi : i = base
    · subst i
      rw [hw, hv, dist_self]
      exact hr
    · have hbi := hb ⟨i, hi⟩
      simp only [w, dite_eq_right hi, Real.dist_eq, abs_lt]
      constructor <;> linarith [hbi.1, hbi.2]
  have hwU : w ∈ U := hball ((dist_pi_lt_iff hr).mpr hdist)
  refine ⟨w, hwU, hw, ?_⟩
  have he : (fun i : {i : ι // i ≠ base} => w i) = u := by
    funext i
    simp only [w, i.property, ↓reduceDIte]
  exact he.symm ▸ hu

theorem exists_normalized (base : ι) :
    ∃ w : ι → ℝ, w base = 1 ∧ AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => w i) := by
  obtain ⟨w, _, hw⟩ := exists_normalized_near (K := K) base (fun _ => 1) rfl univ Filter.univ_mem
  exact ⟨w, hw⟩

end LeanCanny.Geometry.IndependentRealDirections
