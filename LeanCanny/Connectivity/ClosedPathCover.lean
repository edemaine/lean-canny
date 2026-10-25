/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Logic.Relation

/-! # Connectivity from a finite closed path cover

A finite closed cover by path-connected pieces has exactly the connectivity
of its intersection graph. Apply the theorem to the subtype of the original
space to use relative closedness. Both point reachability and whole-space
connectivity are recovered, including the empty space.

This is a topological transfer lemma, not a construction of such a cover from
a polynomial formula or a bound on its representation.
-/

@[expose] public section

namespace LeanCanny.Connectivity.ClosedPathCover
open Set

variable {ι X : Type*} [TopologicalSpace X] (piece : ι → Set X)

/-- The intersection graph; empty pieces have no edges. -/
def Overlap (i j : ι) : Prop := (piece i ∩ piece j).Nonempty

private def cluster (i : ι) : Set X :=
  {x | ∃ j, Relation.ReflTransGen (Overlap piece) i j ∧ x ∈ piece j}

private theorem cluster_isClopen [Finite ι] (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i) (i : ι) : IsClopen (cluster piece i) := by
  classical
  have hc : IsClosed (cluster piece i) := by
    convert isClosed_iUnion_of_finite
      (fun j : {j // Relation.ReflTransGen (Overlap piece) i j} => closed j.val) using 1
    ext x
    simp [cluster]
  have heq : (cluster piece i)ᶜ =
      ⋃ j : {j // ¬ Relation.ReflTransGen (Overlap piece) i j}, piece j.val := by
    ext x
    simp only [mem_compl_iff, cluster, mem_ofPred_eq, mem_iUnion, Subtype.exists,
      exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := cover x
      exact ⟨j, fun hr => hx ⟨j, hr, hj⟩, hj⟩
    · rintro ⟨j, hj, hxj⟩ ⟨k, hk, hxk⟩
      exact hj (hk.tail ⟨x, hxk, hxj⟩)
  refine ⟨hc, ?_⟩
  rw [← isClosed_compl_iff, heq]
  exact isClosed_iUnion_of_finite (fun j => closed j.val)

/-- Every graph walk gives an actual path, by joining through intersections.
Closedness and finiteness are unnecessary for this direction. -/
theorem joinedIn_of_reachable
    (paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j)
    (hr : Relation.ReflTransGen (Overlap piece) i j) : JoinedIn univ x y := by
  induction hr generalizing y with
  | refl => exact (paths _ x hx y hy).mono (subset_univ _)
  | @tail j k hr he ih =>
    obtain ⟨z, hzj, hzk⟩ := he
    exact (ih hzj).trans ((paths k z hzk y hy).mono (subset_univ _))

/-- A path cannot cross between the clopen graph clusters of a finite closed
cover. The path-connectedness of individual pieces is unnecessary here. -/
theorem reachable_of_joinedIn [Finite ι] (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i) {i j : ι} {x y : X}
    (hx : x ∈ piece i) (hy : y ∈ piece j) (h : JoinedIn univ x y) :
    Relation.ReflTransGen (Overlap piece) i j := by
  obtain ⟨γ, _⟩ := h
  have hx' : x ∈ cluster piece i := ⟨i, .refl, hx⟩
  have hsub := (isPreconnected_range γ.continuous).subset_isClopen
    (cluster_isClopen piece closed cover i) ⟨x, γ.source_mem_range, hx'⟩
  obtain ⟨k, hk, hyk⟩ := hsub γ.target_mem_range
  exact hk.tail ⟨y, hyk, hy⟩

theorem joinedIn_iff_reachable [Finite ι] (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i)
    (paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (Overlap piece) i j :=
  ⟨reachable_of_joinedIn piece closed cover hx hy,
    joinedIn_of_reachable piece paths hx hy⟩

/-- Topological whole-space connectivity is exactly graph connectivity on the
nonempty pieces. The statement also holds when there are no points or pieces. -/
theorem isPreconnected_iff_reachable [Finite ι] (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i)
    (paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y) :
    IsPreconnected (univ : Set X) ↔
      ∀ i j, (piece i).Nonempty → (piece j).Nonempty →
        Relation.ReflTransGen (Overlap piece) i j := by
  constructor
  · intro h i j hi hj
    obtain ⟨x, hx⟩ := hi
    obtain ⟨y, hy⟩ := hj
    have hsub := h.subset_isClopen (cluster_isClopen piece closed cover i)
      ⟨x, mem_univ x, i, .refl, hx⟩
    obtain ⟨k, hk, hyk⟩ := hsub (mem_univ y)
    exact hk.tail ⟨y, hyk, hy⟩
  · intro h
    apply isPreconnected_of_forall_pair
    intro x hx y hy
    obtain ⟨i, hi⟩ := cover x
    obtain ⟨j, hj⟩ := cover y
    obtain ⟨γ, _⟩ := joinedIn_of_reachable piece paths hi hj (h i j ⟨x, hi⟩ ⟨y, hj⟩)
    exact ⟨Set.range γ, subset_univ _, γ.source_mem_range, γ.target_mem_range,
      isPreconnected_range γ.continuous⟩

end LeanCanny.Connectivity.ClosedPathCover
