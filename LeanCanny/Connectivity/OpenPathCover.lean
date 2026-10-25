/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ClosedPathCover

/-! # Paths through an arbitrary open cover

An open cover need not have finitely many pieces: its overlap-graph clusters
are clopen even for an infinite index set. Every path therefore induces a
finite graph walk. Path connectivity of the individual pieces is needed only
for the converse direction.
-/

@[expose] public section

namespace LeanCanny.Connectivity.OpenPathCover
open Set
open ClosedPathCover (Overlap)

variable {ι X : Type*} [TopologicalSpace X] (piece : ι → Set X)

private def cluster (i : ι) : Set X :=
  {x | ∃ j, Relation.ReflTransGen (Overlap piece) i j ∧ x ∈ piece j}

private theorem cluster_isClopen (hopen : ∀ i, IsOpen (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i) (i : ι) : IsClopen (cluster piece i) := by
  have heq : cluster piece i =
      ⋃ j : {j // Relation.ReflTransGen (Overlap piece) i j}, piece j.val := by
    ext x
    simp [cluster]
  have hcompl : (cluster piece i)ᶜ =
      ⋃ j : {j // ¬ Relation.ReflTransGen (Overlap piece) i j}, piece j.val := by
    ext x
    simp only [mem_compl_iff, cluster, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := cover x
      exact ⟨j, fun hr => hx ⟨j, hr, hj⟩, hj⟩
    · rintro ⟨j, hj, hxj⟩ ⟨k, hk, hxk⟩
      exact hj (hk.tail ⟨x, hxk, hxj⟩)
  have ho : IsOpen (cluster piece i) := by
    rw [heq]
    exact isOpen_iUnion (fun j => hopen j.val)
  refine ⟨?_, ho⟩
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion (fun j => hopen j.val)

/-- A connected subset of an open cover lies in a single graph cluster. -/
theorem reachable_of_isPreconnected (hopen : ∀ i, IsOpen (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i) {s : Set X} (hs : IsPreconnected s)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j)
    (hxs : x ∈ s) (hys : y ∈ s) :
    Relation.ReflTransGen (Overlap piece) i j := by
  have hsub := hs.subset_isClopen (cluster_isClopen piece hopen cover i) ⟨x, hxs, i, .refl, hx⟩
  obtain ⟨k, hk, hyk⟩ := hsub hys
  exact hk.tail ⟨y, hyk, hy⟩

/-- No finiteness or path-connectivity assumption on the cover is needed. -/
theorem reachable_of_joinedIn (hopen : ∀ i, IsOpen (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i) {i j : ι} {x y : X}
    (hx : x ∈ piece i) (hy : y ∈ piece j) (h : JoinedIn univ x y) :
    Relation.ReflTransGen (Overlap piece) i j := by
  obtain ⟨γ, _⟩ := h
  exact reachable_of_isPreconnected piece hopen cover (isPreconnected_range γ.continuous)
    hx hy γ.source_mem_range γ.target_mem_range

theorem joinedIn_iff_reachable (hopen : ∀ i, IsOpen (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i)
    (paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (Overlap piece) i j :=
  ⟨reachable_of_joinedIn piece hopen cover hx hy,
    ClosedPathCover.joinedIn_of_reachable piece paths hx hy⟩

end LeanCanny.Connectivity.OpenPathCover
