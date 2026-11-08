/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitFrontierCover
public import LeanCanny.Computation.MarkedGraphPSPACE

/-! # Marked component tests in finite accessible covers

Only pieces meeting the marked subset are endpoint candidates. The graph
keeps every valid piece available for traversal. The native space theorem
charges edge, validity and marking routines separately; constructing the
actual recursive cover and its query writers remains an obligation.
-/

@[expose] public section
namespace LeanCanny.Connectivity.BitFrontierCover
open Set Computation Turing.MultiTapeTM
open scoped Classical

variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edge : List Bool → List Bool → Bool} {valid : List Bool → Bool}
  (C : BitFrontierCover X w edge valid)

theorem component_eq_connectedComponent {i : Vertex w} {x : X} (hx : x ∈ C.piece i) :
    C.componentCover.piece i = connectedComponent x := by
  have hxi : x ∈ C.componentCover.piece i := ⟨i, .refl, hx⟩
  have hp : IsPathConnected (C.componentCover.piece i) :=
    ⟨x, hxi, fun _ hy => C.componentCover.paths i x hxi _ hy⟩
  exact (hp.isConnected.isPreconnected.subset_connectedComponent hxi).antisymm
    ((C.componentCover.clopen i).connectedComponent_subset hxi)

theorem component_iff_reachable {u v : List Bool} (hu : u.length = w) (hv : v.length = w)
    {x y : X} (hx : x ∈ C.piece ⟨u, hu⟩) (hy : y ∈ C.piece ⟨v, hv⟩) :
    y ∈ connectedComponent x ↔ ImplicitGraph.Reachable edge valid w u v := by
  rw [← C.component_eq_connectedComponent hx]
  exact C.mem_component_iff_reachable hu hv hy

theorem marked_components_iff_connected (S : Set X) (marked : List Bool → Bool)
    (hm : ∀ i : Vertex w, marked i.val = true ↔ (C.piece i ∩ S).Nonempty) :
    (∀ x ∈ S, ∀ y ∈ S, y ∈ connectedComponent x) ↔ ImplicitGraph.MarkedConnected edge valid marked w := by
  constructor
  · intro h u hu v hv hmu hmv
    obtain ⟨x, hxi, hxs⟩ := (hm ⟨u, hu⟩).mp hmu
    obtain ⟨y, hyi, hys⟩ := (hm ⟨v, hv⟩).mp hmv
    exact (C.component_iff_reachable hu hv hxi hyi).mp (h x hxs y hys)
  · intro h x hxs y hys
    obtain ⟨i, hxi⟩ := C.cover x
    obtain ⟨j, hyj⟩ := C.cover y
    apply (C.component_iff_reachable i.property j.property hxi hyj).mpr
    exact h i.val i.property j.val j.property ((hm i).mpr ⟨x, hxi, hxs⟩) ((hm j).mpr ⟨y, hyj, hys⟩)

section Computability
variable {α : Type} [Inhabited α] {eA : α ↪ List Bool} {Y : α → Type*} [∀ c, TopologicalSpace (Y c)]
  {edges : α → List Bool → List Bool → Bool} {valids marks : α → List Bool → Bool} {width : α → ℕ}
  (covers : ∀ c, BitFrontierCover (Y c) (width c) (edges c) (valids c)) (sets : ∀ c, Set (Y c))

theorem marked_components_computable
    (hmarks : ∀ c (i : Vertex (width c)), marks c i.val = true ↔ ((covers c).piece i ∩ sets c).Nonempty)
    (he : ComputableInPolySpace (fun p : α × List Bool × List Bool => edges p.1 p.2.1 p.2.2)
      (encPair eA (encPair encBits encBits)) encBool)
    (hv : ComputableInPolySpace (fun p : α × List Bool => valids p.1 p.2) (encPair eA encBits) encBool)
    (hm : ComputableInPolySpace (fun p : α × List Bool => marks p.1 p.2) (encPair eA encBits) encBool)
    (hw : ComputableTidilyInPolyTime width eA encUnary) :
    ComputableInPolySpace
      (fun c => decide (∀ x ∈ sets c, ∀ y ∈ sets c, y ∈ connectedComponent x)) eA encBool := by
  apply (ImplicitGraph.marked_connected_computable he hv hm hw).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ((covers c).marked_components_iff_connected (sets c) (marks c) (hmarks c)).symm

end Computability
end LeanCanny.Connectivity.BitFrontierCover
