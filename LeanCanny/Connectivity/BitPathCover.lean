/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ClosedPathCover
public import LeanCanny.Computation.ImplicitGraphPSPACE

/-! # Bit-indexed covers and implicit graph algorithms

This connects the topological cover theorem to the actual fixed-width Savitch
algorithm. Invalid vertex records denote empty pieces. A cover can have
exponentially many pieces; its Boolean edge and validity routines are charged
in full by the polynomial-space theorems below.

Constructing these covers effectively for semialgebraic inputs is a separate,
still unresolved obligation. No such construction is assumed to exist here.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open Set Computation
open Turing.MultiTapeTM
open scoped Classical

abbrev Vertex (w : ℕ) := {u : List Bool // u.length = w}

instance (w : ℕ) : Finite (Vertex w) := by
  have h : {u : List Bool | u.length = w}.Finite := by
    simpa only [Cslib.BitString.mem_enumList] using
      (Cslib.BitString.enumList w).finite_toSet
  exact h.to_subtype

/-- A finite closed path cover with a Boolean intersection graph. Empty pieces
are permitted, and are precisely the invalid vertex words. -/
structure BitPathCover (X : Type*) [TopologicalSpace X] (w : ℕ)
    (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool) where
  piece : Vertex w → Set X
  closed : ∀ i, IsClosed (piece i)
  cover : ∀ x, ∃ i, x ∈ piece i
  paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y
  valid_iff : ∀ i, valid i.val = true ↔ (piece i).Nonempty
  edge_iff : ∀ i j, edge i.val j.val = true ↔ (piece i ∩ piece j).Nonempty

namespace BitPathCover
variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edge : List Bool → List Bool → Bool} {valid : List Bool → Bool}
  (C : BitPathCover X w edge valid)

private theorem step_iff {i j : Vertex w} :
    ImplicitGraph.Step (ImplicitGraph.guard edge valid) w i.val j.val ↔
      ClosedPathCover.Overlap C.piece i j := by
  constructor
  · rintro ⟨_, _, h⟩
    simp only [ImplicitGraph.guard, Bool.and_eq_true] at h
    exact (C.edge_iff i j).mp h.2
  · rintro ⟨x, hx, hy⟩
    exact ⟨i.property, j.property, by
      simp [ImplicitGraph.guard, (C.valid_iff i).mpr ⟨x, hx⟩,
        (C.valid_iff j).mpr ⟨x, hy⟩, (C.edge_iff i j).mpr ⟨x, hx, hy⟩]⟩

private theorem walk_iff {u v : List Bool} (hu : u.length = w) (hv : v.length = w) :
    Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard edge valid) w) u v ↔
      Relation.ReflTransGen (ClosedPathCover.Overlap C.piece) ⟨u, hu⟩ ⟨v, hv⟩ := by
  constructor
  · intro h
    have lift : ∀ {z},
        Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard edge valid) w) u z →
        ∀ hz : z.length = w,
          Relation.ReflTransGen (ClosedPathCover.Overlap C.piece) ⟨u, hu⟩ ⟨z, hz⟩ := by
      intro z hz
      induction hz with
      | refl => intro _; exact .refl
      | tail _ he ih =>
        intro hz'
        exact (ih he.1).tail ((C.step_iff).mp he)
    exact lift h hv
  · intro h
    exact h.lift Subtype.val (fun _ _ he => C.step_iff.mpr he)

/-- Membership in the endpoint pieces ensures endpoint validity. The graph
test also guards every intermediate vertex. -/
theorem joinedIn_iff_reachable {u v : List Bool} (hu : u.length = w) (hv : v.length = w)
    {x y : X} (hx : x ∈ C.piece ⟨u, hu⟩) (hy : y ∈ C.piece ⟨v, hv⟩) :
    JoinedIn univ x y ↔ ImplicitGraph.Reachable edge valid w u v := by
  rw [ClosedPathCover.joinedIn_iff_reachable C.piece C.closed C.cover C.paths hx hy,
    ← C.walk_iff hu hv]
  have hU := (C.valid_iff ⟨u, hu⟩).mpr ⟨x, hx⟩
  have hV := (C.valid_iff ⟨v, hv⟩).mpr ⟨y, hy⟩
  simp [ImplicitGraph.Reachable, hU, hV]

include C in
/-- Topological connectivity equals the algorithm's whole-graph predicate,
including the empty space and width zero. -/
theorem isPreconnected_iff_connected :
    IsPreconnected (univ : Set X) ↔ ImplicitGraph.Connected edge valid w := by
  rw [ClosedPathCover.isPreconnected_iff_reachable C.piece C.closed C.cover C.paths]
  constructor
  · intro h u hu v hv hU hV
    exact (C.walk_iff hu hv).mpr
      (h ⟨u, hu⟩ ⟨v, hv⟩ ((C.valid_iff _).mp hU) ((C.valid_iff _).mp hV))
  · intro h i j hi hj
    exact (C.walk_iff i.property j.property).mp
      (h i.val i.property j.val j.property ((C.valid_iff _).mpr hi) ((C.valid_iff _).mpr hj))

section Computability
variable {α : Type} {eA : α ↪ List Bool} {Y : α → Type*}
  [∀ c, TopologicalSpace (Y c)]
  {edges : α → List Bool → List Bool → Bool} {valids : α → List Bool → Bool}
  {width : α → ℕ} (covers : ∀ c, BitPathCover (Y c) (width c) (edges c) (valids c))
  (he : ComputableInPolySpace
    (fun p : α × List Bool × List Bool => edges p.1 p.2.1 p.2.2)
    (encPair eA (encPair encBits encBits)) encBool)
  (hv : ComputableInPolySpace (fun p : α × List Bool => valids p.1 p.2)
    (encPair eA encBits) encBool)
  (hw : ComputableTidilyInPolyTime width eA encUnary)

include covers he hv hw

/-- A supplied cover with effective graph routines gives a native polynomial-
space whole-space connectivity test. This does not construct the cover. -/
theorem connected_computable [Inhabited α] :
    ComputableInPolySpace
      (fun c => decide (IsPreconnected (univ : Set (Y c)))) eA encBool := by
  apply (ImplicitGraph.connected_computable he hv hw).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (covers c).isPreconnected_iff_connected.symm

/-- Point connectivity uses polynomial-space piece identifiers. The actual
points are mathematical parameters and need not have rational coordinates. -/
theorem joinedIn_computable {src dst : α → List Bool}
    (hs : ComputableInPolySpace src eA encBits)
    (hd : ComputableInPolySpace dst eA encBits)
    (hsrc : ∀ c, (src c).length = width c) (hdst : ∀ c, (dst c).length = width c)
    {x y : (c : α) → Y c}
    (hx : ∀ c, x c ∈ (covers c).piece ⟨src c, hsrc c⟩)
    (hy : ∀ c, y c ∈ (covers c).piece ⟨dst c, hdst c⟩) :
    ComputableInPolySpace
      (fun c => decide (JoinedIn univ (x c) (y c))) eA encBool := by
  apply (ImplicitGraph.reachable_computable he hv hw hs hd hsrc hdst).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ((covers c).joinedIn_iff_reachable (hsrc c) (hdst c) (hx c) (hy c)).symm

end Computability
end BitPathCover
end LeanCanny.Connectivity
