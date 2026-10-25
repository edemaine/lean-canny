/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitPathCover
public import LeanCanny.Connectivity.FrontierCover
public import LeanCanny.Connectivity.ClopenPathCover

/-! # Polynomial-space connectivity from effective frontier covers

This is the native implicit-graph transfer for nonclosed pieces. Its edge
routine tests relative frontier incidence; its workspace is charged in full.
The geometric construction and the space bounds for this routine must be
supplied for each input family. No effective semialgebraic cover is assumed.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open Set Computation
open Turing.MultiTapeTM
open scoped Classical

/-- A finite accessible cover encoded by fixed-width vertex words. Closures
are relative to `X`, so omitted boundary points create no edges. -/
structure BitFrontierCover (X : Type*) [TopologicalSpace X] (w : ℕ)
    (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool) where
  piece : Vertex w → Set X
  cover : ∀ x, ∃ i, x ∈ piece i
  accessible : ∀ i, FrontierCover.Accessible (piece i)
  valid_iff : ∀ i, valid i.val = true ↔ (piece i).Nonempty
  edge_iff : ∀ i j, edge i.val j.val = true ↔ FrontierCover.Incident piece i j

namespace BitFrontierCover
variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edge : List Bool → List Bool → Bool} {valid : List Bool → Bool}
  (C : BitFrontierCover X w edge valid)

private theorem step_iff {i j : Vertex w} :
    ImplicitGraph.Step (ImplicitGraph.guard edge valid) w i.val j.val ↔
      FrontierCover.Incident C.piece i j := by
  constructor
  · rintro ⟨_, _, h⟩
    simp only [ImplicitGraph.guard, Bool.and_eq_true] at h
    exact (C.edge_iff i j).mp h.2
  · intro h
    have hn := h.nonempty C.piece
    exact ⟨i.property, j.property, by
      simp [ImplicitGraph.guard, (C.valid_iff i).mpr hn.1,
        (C.valid_iff j).mpr hn.2, (C.edge_iff i j).mpr h]⟩

private theorem walk_iff {u v : List Bool} (hu : u.length = w) (hv : v.length = w) :
    Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard edge valid) w) u v ↔
      Relation.ReflTransGen (FrontierCover.Incident C.piece) ⟨u, hu⟩ ⟨v, hv⟩ := by
  constructor
  · intro h
    have lift : ∀ {z},
        Relation.ReflTransGen (ImplicitGraph.Step (ImplicitGraph.guard edge valid) w) u z →
        ∀ hz : z.length = w,
          Relation.ReflTransGen (FrontierCover.Incident C.piece) ⟨u, hu⟩ ⟨z, hz⟩ := by
      intro z hz
      induction hz with
      | refl => intro _; exact .refl
      | tail _ he ih =>
        intro hz'
        exact (ih he.1).tail ((C.step_iff).mp he)
    exact lift h hv
  · intro h
    exact h.lift Subtype.val (fun _ _ he => C.step_iff.mpr he)

theorem joinedIn_iff_reachable {u v : List Bool} (hu : u.length = w) (hv : v.length = w)
    {x y : X} (hx : x ∈ C.piece ⟨u, hu⟩) (hy : y ∈ C.piece ⟨v, hv⟩) :
    JoinedIn univ x y ↔ ImplicitGraph.Reachable edge valid w u v := by
  rw [FrontierCover.joinedIn_iff_reachable C.piece C.cover C.accessible hx hy,
    ← C.walk_iff hu hv]
  have hU := (C.valid_iff ⟨u, hu⟩).mpr ⟨x, hx⟩
  have hV := (C.valid_iff ⟨v, hv⟩).mpr ⟨y, hy⟩
  simp [ImplicitGraph.Reachable, hU, hV]

include C in
theorem isPreconnected_iff_connected :
    IsPreconnected (univ : Set X) ↔ ImplicitGraph.Connected edge valid w := by
  rw [FrontierCover.isPreconnected_iff_reachable C.piece C.cover C.accessible]
  constructor
  · intro h u hu v hv hU hV
    exact (C.walk_iff hu hv).mpr
      (h ⟨u, hu⟩ ⟨v, hv⟩ ((C.valid_iff _).mp hU) ((C.valid_iff _).mp hV))
  · intro h i j hi hj
    exact (C.walk_iff i.property j.property).mp
      (h i.val i.property j.val j.property ((C.valid_iff _).mpr hi) ((C.valid_iff _).mpr hj))

/-- Recursive graph saturation gives actual clopen path pieces with the same
fixed-width labels. No quotient labels or component oracle are introduced. -/
def componentCover : ClopenPathCover X (Vertex w) :=
  ClopenPathCover.ofAccessible C.piece C.cover C.accessible

theorem mem_component_iff_reachable {u v : List Bool} (hu : u.length = w) (hv : v.length = w)
    {x : X} (hx : x ∈ C.piece ⟨v, hv⟩) :
    x ∈ C.componentCover.piece ⟨u, hu⟩ ↔ ImplicitGraph.Reachable edge valid w u v := by
  have hV := (C.valid_iff ⟨v, hv⟩).mpr ⟨x, hx⟩
  constructor
  · rintro hm
    have hU := (C.valid_iff ⟨u, hu⟩).mpr
      ((FrontierCover.component_nonempty_iff C.piece ⟨u, hu⟩).mp ⟨x, hm⟩)
    obtain ⟨j, hj, hxj⟩ := hm
    have hr := hj.tail (Or.inl ⟨x, hxj, subset_closure hx⟩)
    exact ⟨hU, hV, (C.walk_iff hu hv).mpr hr⟩
  · rintro ⟨_, _, hr⟩
    exact ⟨⟨v, hv⟩, (C.walk_iff hu hv).mp hr, hx⟩

section Computability
variable {α : Type} {eA : α ↪ List Bool} {Y : α → Type*}
  [∀ c, TopologicalSpace (Y c)]
  {edges : α → List Bool → List Bool → Bool} {valids : α → List Bool → Bool}
  {width : α → ℕ} (covers : ∀ c, BitFrontierCover (Y c) (width c) (edges c) (valids c))
  (he : ComputableTidilyInPolySpace
    (fun p : α × List Bool × List Bool => edges p.1 p.2.1 p.2.2)
    (encPair eA (encPair encBits encBits)) encBool)
  (hv : ComputableTidilyInPolySpace (fun p : α × List Bool => valids p.1 p.2)
    (encPair eA encBits) encBool)
  (hw : ComputableTidilyInPolyTime width eA encUnary)

include covers he hv hw

/-- Native PSPACE accounts for all workspace of frontier adjacency and validity. -/
theorem connected_computable [Inhabited α] :
    ComputableTidilyInPolySpace
      (fun c => decide (IsPreconnected (univ : Set (Y c)))) eA encBool := by
  apply (ImplicitGraph.connected_computable he hv hw).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (covers c).isPreconnected_iff_connected.symm

/-- Polynomial-space endpoint locators suffice; coordinates may be irrational. -/
theorem joinedIn_computable {src dst : α → List Bool}
    (hs : ComputableTidilyInPolySpace src eA encBits)
    (hd : ComputableTidilyInPolySpace dst eA encBits)
    (hsrc : ∀ c, (src c).length = width c) (hdst : ∀ c, (dst c).length = width c)
    {x y : (c : α) → Y c}
    (hx : ∀ c, x c ∈ (covers c).piece ⟨src c, hsrc c⟩)
    (hy : ∀ c, y c ∈ (covers c).piece ⟨dst c, hdst c⟩) :
    ComputableTidilyInPolySpace
      (fun c => decide (JoinedIn univ (x c) (y c))) eA encBool := by
  apply (ImplicitGraph.reachable_computable he hv hw hs hd hsrc hdst).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ((covers c).joinedIn_iff_reachable (hsrc c) (hdst c) (hx c) (hy c)).symm

/-- Membership in a recursive clopen component is in native polynomial space
once an original piece containing the queried point can be located. Invalid
component records are rejected by the same guarded reachability algorithm. -/
theorem component_membership_computable {label src : α → List Bool}
    (hl : ComputableTidilyInPolySpace label eA encBits)
    (hs : ComputableTidilyInPolySpace src eA encBits)
    (hlabel : ∀ c, (label c).length = width c) (hsrc : ∀ c, (src c).length = width c)
    {x : (c : α) → Y c} (hx : ∀ c, x c ∈ (covers c).piece ⟨src c, hsrc c⟩) :
    ComputableTidilyInPolySpace
      (fun c => decide (x c ∈ (covers c).componentCover.piece ⟨label c, hlabel c⟩)) eA encBool := by
  apply (ImplicitGraph.reachable_computable he hv hw hl hs hlabel hsrc).congr
  intro c
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ((covers c).mem_component_iff_reachable (hlabel c) (hsrc c) (hx c)).symm

end Computability
end BitFrontierCover

namespace BitPathCover
variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edge : List Bool → List Bool → Bool} {valid : List Bool → Bool}

/-- Closed path covers use exactly their existing overlap routine for frontier
incidence. Thus the native component-membership theorem applies at the next
recursive slice level without adding a closure oracle. -/
def toFrontierCover (C : BitPathCover X w edge valid) : BitFrontierCover X w edge valid where
  piece := C.piece
  cover := C.cover
  accessible := fun i x hx y hy => by
    have hx' : x ∈ C.piece i := (C.closed i).closure_eq ▸ hx
    simpa only [insert_eq_of_mem hx'] using C.paths i x hx' y hy
  valid_iff := C.valid_iff
  edge_iff := by
    intro i j
    rw [C.edge_iff]
    simp only [FrontierCover.Incident, (C.closed i).closure_eq, (C.closed j).closure_eq]
    constructor
    · exact Or.inl
    · rintro (⟨x, hi, hj⟩ | ⟨x, hj, hi⟩) <;> exact ⟨x, hi, hj⟩

end BitPathCover
end LeanCanny.Connectivity
