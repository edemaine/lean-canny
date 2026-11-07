/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ClosedPathCover

/-! # Connectivity through frontiers of a finite decomposition

Strata and cells need not be relatively closed. Their incidence graph must
therefore record a point of one piece in the relative closure of another.
All closures in this file are taken in the ambient type; use the subtype of
the described space so excluded boundary points cannot create false edges.

Graph connectivity follows from preconnectedness of the pieces. To recover
paths we additionally require access from each relative boundary point by a
path whose other points remain in that piece. The geometric curve-selection
and effective decomposition results are separate obligations.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FrontierCover
open Set

variable {ι X : Type*} [TopologicalSpace X] (piece : ι → Set X)

/-- An undirected boundary incidence, including ordinary intersections. -/
def Incident (i j : ι) : Prop :=
  (piece i ∩ closure (piece j)).Nonempty ∨ (piece j ∩ closure (piece i)).Nonempty

theorem incident_symm {i j : ι} : Incident piece i j ↔ Incident piece j i := or_comm

instance : Std.Symm (Incident piece) where
  symm _ _ := (incident_symm piece).mp

theorem Incident.nonempty {i j : ι} (h : Incident piece i j) :
    (piece i).Nonempty ∧ (piece j).Nonempty := by
  rcases h with ⟨x, hx, hy⟩ | ⟨x, hy, hx⟩
  · exact ⟨⟨x, hx⟩, (show (closure (piece j)).Nonempty from ⟨x, hy⟩).of_closure⟩
  · exact ⟨(show (closure (piece i)).Nonempty from ⟨x, hx⟩).of_closure, ⟨x, hy⟩⟩

/-- Saturate a piece by its finite frontier-graph component. Keeping the
original labels avoids choosing representatives or discarding empty records. -/
def component (i : ι) : Set X :=
  {x | ∃ j, Relation.ReflTransGen (Incident piece) i j ∧ x ∈ piece j}

theorem component_isClopen [Finite ι]
    (cover : ∀ x, ∃ i, x ∈ piece i) (i : ι) : IsClopen (component piece i) := by
  classical
  have hcluster : component piece i =
      ⋃ j : {j // Relation.ReflTransGen (Incident piece) i j}, closure (piece j.val) := by
    ext x
    simp only [component, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, subset_closure hx⟩
    · rintro ⟨j, hj, hx⟩
      obtain ⟨k, hk⟩ := cover x
      exact ⟨k, hj.tail (Or.inr ⟨x, hk, hx⟩), hk⟩
  have hcompl : (component piece i)ᶜ =
      ⋃ j : {j // ¬ Relation.ReflTransGen (Incident piece) i j}, closure (piece j.val) := by
    ext x
    simp only [mem_compl_iff, component, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := cover x
      exact ⟨j, fun hr => hx ⟨j, hr, hj⟩, subset_closure hj⟩
    · rintro ⟨j, hj, hx⟩ ⟨k, hk, hxk⟩
      exact hj (hk.tail (Or.inl ⟨x, hxk, hx⟩))
  refine ⟨?_, ?_⟩
  · rw [hcluster]
    exact isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  · rw [← isClosed_compl_iff, hcompl]
    exact isClosed_iUnion_of_finite (fun _ => isClosed_closure)

/-- A preconnected subset cannot meet different graph clusters. Neither
path accessibility nor preconnectedness of individual pieces is needed here. -/
theorem reachable_of_isPreconnected [Finite ι]
    (cover : ∀ x, ∃ i, x ∈ piece i) {s : Set X} (hs : IsPreconnected s)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j)
    (hxs : x ∈ s) (hys : y ∈ s) :
    Relation.ReflTransGen (Incident piece) i j := by
  have hsub := hs.subset_isClopen (component_isClopen piece cover i)
    ⟨x, hxs, i, .refl, hx⟩
  obtain ⟨k, hk, hyk⟩ := hsub hys
  exact hk.tail (Or.inl ⟨y, hyk, subset_closure hy⟩)

/-- Every path induces a walk in the finite frontier-incidence graph. -/
theorem reachable_of_joinedIn [Finite ι] (cover : ∀ x, ∃ i, x ∈ piece i)
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j)
    (h : JoinedIn univ x y) : Relation.ReflTransGen (Incident piece) i j := by
  obtain ⟨γ, _⟩ := h
  exact reachable_of_isPreconnected piece cover (isPreconnected_range γ.continuous)
    hx hy γ.source_mem_range γ.target_mem_range

/-- A single piece can be approached from every point of its relative closure,
with a path contained in that piece apart from its new starting point. -/
def Accessible (s : Set X) : Prop :=
  ∀ x ∈ closure s, ∀ y ∈ s, JoinedIn (insert x s) x y

theorem accessible_singleton [T1Space X] (x : X) : Accessible ({x} : Set X) := by
  intro y hy z hz
  rw [closure_singleton, mem_singleton_iff] at hy
  rw [mem_singleton_iff] at hz
  subst y
  subst z
  exact JoinedIn.refl (mem_insert _ _)

theorem Accessible.isPreconnected {s : Set X} (h : Accessible s) : IsPreconnected s := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨γ, hγ⟩ := h x (subset_closure hx) y hy
  have hsub : range γ ⊆ s := by
    rintro z ⟨t, rfl⟩
    simpa only [insert_eq_of_mem hx] using hγ t
  exact ⟨range γ, hsub, γ.source_mem_range, γ.target_mem_range,
    isPreconnected_range γ.continuous⟩

/-- Boundary accessibility turns each incidence into an actual path. -/
theorem joinedIn_of_reachable
    (access : ∀ i, Accessible (piece i))
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j)
    (h : Relation.ReflTransGen (Incident piece) i j) : JoinedIn univ x y := by
  induction h generalizing y with
  | refl => exact (access _ x (subset_closure hx) y hy).mono (subset_univ _)
  | @tail j k hr he ih =>
    rcases he with ⟨z, hzj, hzk⟩ | ⟨z, hzk, hzj⟩
    · exact (ih hzj).trans ((access k z hzk y hy).mono (subset_univ _))
    · -- Join first to a point of `j`, then to its accessible boundary point.
      obtain ⟨a, ha⟩ : (piece j).Nonempty := by
        have hne : (closure (piece j)).Nonempty := ⟨z, hzj⟩
        exact hne.of_closure
      exact ((ih ha).trans (((access j z hzj a ha).mono (subset_univ _)).symm)).trans
        ((access k z (subset_closure hzk) y hy).mono (subset_univ _))

theorem joinedIn_iff_reachable [Finite ι] (cover : ∀ x, ∃ i, x ∈ piece i)
    (access : ∀ i, Accessible (piece i))
    {i j : ι} {x y : X} (hx : x ∈ piece i) (hy : y ∈ piece j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (Incident piece) i j :=
  ⟨reachable_of_joinedIn piece cover hx hy, joinedIn_of_reachable piece access hx hy⟩

/-- A recursively supplied accessible cover converts connection inside any
preconnected subset into an actual path in the original ambient space. -/
theorem joinedIn_of_isPreconnected [Finite ι] (cover : ∀ x, ∃ i, x ∈ piece i)
    (access : ∀ i, Accessible (piece i)) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : JoinedIn univ x y := by
  obtain ⟨i, hi⟩ := cover x
  obtain ⟨j, hj⟩ := cover y
  exact joinedIn_of_reachable piece access hi hj
    (reachable_of_isPreconnected piece cover hs hi hj hx hy)

theorem component_cover (cover : ∀ x, ∃ i, x ∈ piece i) :
    ∀ x, ∃ i, x ∈ component piece i := by
  intro x
  obtain ⟨i, hi⟩ := cover x
  exact ⟨i, i, .refl, hi⟩

theorem component_nonempty_iff (i : ι) : (component piece i).Nonempty ↔ (piece i).Nonempty := by
  constructor
  · rintro ⟨x, j, hj, hx⟩
    rcases hj.cases_head with rfl | ⟨k, hik, _⟩
    · exact ⟨x, hx⟩
    · exact (hik.nonempty piece).1
  · rintro ⟨x, hx⟩
    exact ⟨x, i, .refl, hx⟩

theorem component_paths [Finite ι] (cover : ∀ x, ∃ i, x ∈ piece i)
    (access : ∀ i, Accessible (piece i)) (i : ι)
    (x : X) (hx : x ∈ component piece i) (y : X) (hy : y ∈ component piece i) :
    JoinedIn (component piece i) x y := by
  obtain ⟨j, hj, hxj⟩ := hx
  obtain ⟨k, hk, hyk⟩ := hy
  obtain ⟨γ, _⟩ := joinedIn_of_reachable piece access hxj hyk ((symm hj).trans hk)
  have hsub := (isPreconnected_range γ.continuous).subset_isClopen
    (component_isClopen piece cover i) ⟨x, γ.source_mem_range, j, hj, hxj⟩
  exact ⟨γ, fun t => hsub ⟨t, rfl⟩⟩

/-- An accessible finite decomposition gives the same components as its
frontier-incidence graph, even when the pieces are not closed. -/
theorem isPreconnected_iff_reachable [Finite ι]
    (cover : ∀ x, ∃ i, x ∈ piece i) (access : ∀ i, Accessible (piece i)) :
    IsPreconnected (univ : Set X) ↔
      ∀ i j, (piece i).Nonempty → (piece j).Nonempty →
        Relation.ReflTransGen (Incident piece) i j := by
  constructor
  · intro h i j hi hj
    obtain ⟨x, hx⟩ := hi
    obtain ⟨y, hy⟩ := hj
    exact reachable_of_isPreconnected piece cover h hx hy (mem_univ _) (mem_univ _)
  · intro h
    apply isPreconnected_of_forall_pair
    intro x hx y hy
    obtain ⟨i, hi⟩ := cover x
    obtain ⟨j, hj⟩ := cover y
    obtain ⟨γ, _⟩ := joinedIn_of_reachable piece access hi hj (h i j ⟨x, hi⟩ ⟨y, hj⟩)
    exact ⟨range γ, subset_univ _, γ.source_mem_range, γ.target_mem_range,
      isPreconnected_range γ.continuous⟩

section Images
variable {Y : Type*} [TopologicalSpace Y]

/-- Frontier incidence is unchanged by embedding the ambient space, provided
all pieces lie in its image. This includes relative closures in a subtype. -/
theorem incident_preimage_iff {f : Y → X} (hf : Topology.IsEmbedding f)
    (hsub : ∀ i, piece i ⊆ range f) (i j : ι) :
    Incident (fun k => f ⁻¹' piece k) i j ↔ Incident piece i j := by
  have hcl (k : ι) : closure (f ⁻¹' piece k) = f ⁻¹' closure (piece k) := by
    rw [hf.closure_eq_preimage_closure_image, image_preimage_eq_of_subset (hsub k)]
  simp only [Incident, hcl]
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact Or.inl ⟨f x, hx, hy⟩
    · exact Or.inr ⟨f x, hx, hy⟩
  · rintro (⟨z, hz, hcl⟩ | ⟨z, hz, hcl⟩)
    · obtain ⟨x, rfl⟩ := hsub i hz
      exact Or.inl ⟨x, hz, hcl⟩
    · obtain ⟨x, rfl⟩ := hsub j hz
      exact Or.inr ⟨x, hz, hcl⟩

/-- Closed continuous parametrizations preserve boundary accessibility.
Closedness is what prevents missing limit points of the parametrization. -/
theorem Accessible.image {s : Set X} (hs : Accessible s) {f : X → Y}
    (hf : Continuous f) (hclosed : IsClosedMap f) : Accessible (f '' s) := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hclosed.closure_image_subset s hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h := (hs a ha b hb).map hf.continuousOn
  exact h.mono (by
    rintro z ⟨t, ht, rfl⟩
    rcases ht with rfl | ht
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨t, ht, rfl⟩)

/-- Passing to an embedded ambient subspace retains accessibility for pieces
contained in that subspace. Only relative closure points are used. -/
theorem Accessible.preimage_of_isEmbedding {s : Set Y} (hs : Accessible s)
    {f : X → Y} (hf : Topology.IsEmbedding f) (hsub : s ⊆ range f) :
    Accessible (f ⁻¹' s) := by
  intro x hx y hy
  have hx' : f x ∈ closure s := hf.continuous.closure_preimage_subset s hx
  have h := hs (f x) hx' (f y) hy
  apply (hf.isInducing.joinedIn_image (mem_insert x _) (mem_insert_of_mem x hy)).mp
  simpa only [image_insert_eq, image_preimage_eq_of_subset hsub] using h

theorem Accessible.subtype {S s : Set X} (hs : Accessible s) (hsub : s ⊆ S) :
    Accessible (((↑) : S → X) ⁻¹' s) :=
  hs.preimage_of_isEmbedding Topology.IsEmbedding.subtypeVal (by simpa using hsub)

end Images
end LeanCanny.Connectivity.FrontierCover
