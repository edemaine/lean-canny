/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Bounded
/-! # Exact bounded exhaustion of paths and simultaneous stabilization of finite marked queries

No effective radius is asserted. Every actual path has compact image, and a
single natural radius preserves all path answers among any fixed finite list
of marked points. The statement applies to nonclosed and unbounded sets too.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedPathExhaustion
open Set Metric
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X]

def bounded (S : Set X) (R : ℕ) : Set X := S∩closedBall 0 (R : ℝ)

theorem joined_iff (S : Set X) (x y : X) :
    JoinedIn S x y ↔ ∃ R : ℕ, JoinedIn (bounded S R) x y := by
  constructor
  · rintro ⟨γ,Hγ⟩
    obtain ⟨r,HR⟩ := (isBounded_iff_subset_closedBall (0 : X)).mp (isCompact_range γ.continuous).isBounded
    obtain ⟨R,hR⟩ := exists_nat_ge r
    refine ⟨R,⟨γ,fun t => ⟨Hγ t,?_⟩⟩⟩
    exact closedBall_subset_closedBall hR (HR (mem_range_self t))
  · rintro ⟨_,H⟩
    exact H.mono inter_subset_left

theorem bounded_mono (S : Set X) {R T : ℕ} (h : R≤T) : bounded S R⊆bounded S T :=
  inter_subset_inter_right S (closedBall_subset_closedBall (by exact_mod_cast h))

theorem finite_marked_radius {I : Type*} [Fintype I] (S : Set X) (a : I → X) :
    ∃ R : ℕ, ∀ i j, JoinedIn S (a i) (a j) ↔ JoinedIn (bounded S R) (a i) (a j) := by
  classical
  have HE : ∀ i j, ∃ R : ℕ, JoinedIn S (a i) (a j) → JoinedIn (bounded S R) (a i) (a j) := by
    intro i j
    by_cases H : JoinedIn S (a i) (a j)
    · obtain ⟨R,HR⟩ := (joined_iff S (a i) (a j)).mp H
      exact ⟨R,fun _ => HR⟩
    · exact ⟨0,fun h => (H h).elim⟩
  choose R HR using HE
  refine ⟨∑ i, ∑ j, R i j,fun i j => ⟨fun H => ?_,fun H => H.mono inter_subset_left⟩⟩
  apply (HR i j H).mono (bounded_mono S ?_)
  exact (Finset.single_le_sum (f := R i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k => ∑ j, R k j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

end LeanCanny.Geometry.BoundedPathExhaustion
