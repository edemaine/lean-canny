/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LocalProductFibers
public import LeanCanny.Connectivity.ClosedPathCover

/-! # A finite cover of the original space from fiber-component sections

Saturate each section by the component containing it in each fiber. Transport
makes these pieces clopen. They cover the original total space when the
sections sample every fiber component, and each is path connected by joining
through its section. Overlap is determined by connection of the two samples
in one fixed fiber. This is a geometric reduction; computing the fiber tests
and the section representations remains a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FiberSectionCover
open Set
open Geometry

variable {X B J : Type*} [TopologicalSpace X] [TopologicalSpace B]
  (p : X → B) (sectionMap : J → C(B, X))

def piece (j : J) : Set X :=
  {x | JoinedIn (p ⁻¹' {p x}) (sectionMap j (p x)) x}

def SampleEdge (b : B) (i j : J) : Prop :=
  JoinedIn (p ⁻¹' {b}) (sectionMap i b) (sectionMap j b)

section Geometry
variable [T2Space X] {G : X → Type*} [∀ x, TopologicalSpace (G x)]
  [∀ x, LocallyPathConnectedSpace (G x)]
  (chart : ∀ x, OpenPartialHomeomorph X (B × G x))
  (hsource : ∀ x, x ∈ (chart x).source)
  (hfirst : ∀ a x, x ∈ (chart a).source → (chart a x).1 = p x)
  (hp : IsProperMap p) (hproj : ∀ j b, p (sectionMap j b) = b)

include hsource hfirst hp hproj in
theorem isClopen_piece (j : J) : IsClopen (piece p sectionMap j) :=
  LocalProductFibers.isClopen_joined_along p chart hsource hfirst hp hp.continuous
    ((sectionMap j).continuous.comp hp.continuous) continuous_id (fun x => hproj j (p x)) (fun _ => rfl)

include hproj in
omit [T2Space X] in
theorem section_mem_piece (j : J) (b : B) : sectionMap j b ∈ piece p sectionMap j := by
  change JoinedIn (p ⁻¹' {p (sectionMap j b)}) (sectionMap j (p (sectionMap j b))) (sectionMap j b)
  rw [hproj]
  exact JoinedIn.refl (hproj j b)

variable [PathConnectedSpace B]

include hsource hfirst hp hproj in
omit [PathConnectedSpace B] in
/-- Restricting the parameter to any path-connected region preserves each
saturated component's path connectivity. In particular, short tails are connected. -/
theorem paths_preimage (j : J) {U : Set B} (hU : IsPathConnected U)
    (x : X) (hx : x ∈ piece p sectionMap j ∩ p ⁻¹' U)
    (y : X) (hy : y ∈ piece p sectionMap j ∩ p ⁻¹' U) :
    JoinedIn (piece p sectionMap j ∩ p ⁻¹' U) x y := by
  have hmid : JoinedIn (p ⁻¹' U) (sectionMap j (p x)) (sectionMap j (p y)) := by
    apply ((hU.joinedIn _ hx.2 _ hy.2).map (sectionMap j).continuous.continuousOn).mono
    rintro z ⟨b, hb, rfl⟩
    change p (sectionMap j b) ∈ U
    rwa [hproj]
  have hleft : p ⁻¹' {p x} ⊆ p ⁻¹' U := by
    intro z hz
    change p z ∈ U
    rw [show p z = p x from hz]
    exact hx.2
  have hright : p ⁻¹' {p y} ⊆ p ⁻¹' U := by
    intro z hz
    change p z ∈ U
    rw [show p z = p y from hz]
    exact hy.2
  obtain ⟨γ, hγ⟩ := ((hx.1.mono hleft).symm.trans hmid).trans (hy.1.mono hright)
  have hsub := (isPreconnected_range γ.continuous).subset_isClopen
    (isClopen_piece p sectionMap chart hsource hfirst hp hproj j) ⟨x, γ.source_mem_range, hx.1⟩
  exact ⟨γ, fun t => ⟨hsub ⟨t, rfl⟩, hγ t⟩⟩

include hsource hfirst hp hproj in
omit [PathConnectedSpace B] in
theorem isPathConnected_piece_preimage (j : J) {U : Set B} (hU : IsPathConnected U) :
    IsPathConnected (piece p sectionMap j ∩ p ⁻¹' U) := by
  obtain ⟨b, hb⟩ := hU.nonempty
  refine ⟨sectionMap j b, ⟨section_mem_piece p sectionMap hproj j b, ?_⟩, ?_⟩
  · change p (sectionMap j b) ∈ U
    rwa [hproj]
  · intro y hy
    exact paths_preimage p sectionMap chart hsource hfirst hp hproj j hU _
      ⟨section_mem_piece p sectionMap hproj j b, by change p (sectionMap j b) ∈ U; rwa [hproj]⟩ y hy

include hsource hfirst hp hproj in
/-- Clopenness ensures the paths through a section stay in its saturated piece. -/
theorem paths (j : J) (x : X) (hx : x ∈ piece p sectionMap j)
    (y : X) (hy : y ∈ piece p sectionMap j) : JoinedIn (piece p sectionMap j) x y := by
  have hmid : JoinedIn (univ : Set X) (sectionMap j (p x)) (sectionMap j (p y)) :=
    ((joinedIn_univ.mpr (PathConnectedSpace.joined (p x) (p y))).map
      (sectionMap j).continuous.continuousOn).mono (subset_univ _)
  have h : JoinedIn (univ : Set X) x y :=
    ((hx.mono (subset_univ _)).symm.trans hmid).trans (hy.mono (subset_univ _))
  obtain ⟨γ, _⟩ := h
  have hsub := (isPreconnected_range γ.continuous).subset_isClopen
    (isClopen_piece p sectionMap chart hsource hfirst hp hproj j) ⟨x, γ.source_mem_range, hx⟩
  exact ⟨γ, fun t => hsub ⟨t, rfl⟩⟩

include hsource hfirst hp hproj in
/-- All overlaps of full-dimensional saturated pieces reduce to one fiber. -/
theorem overlap_iff_sample (b₀ : B) (i j : J) :
    ClosedPathCover.Overlap (piece p sectionMap) i j ↔ SampleEdge p sectionMap b₀ i j := by
  constructor
  · rintro ⟨x, hx, hy⟩
    have hj : SampleEdge p sectionMap (p x) i j := hx.trans hy.symm
    exact (LocalProductFibers.joined_sections_iff p chart hsource hfirst hp
      (sectionMap i).continuous (sectionMap j).continuous (hproj i) (hproj j) (p x) b₀).mp hj
  · intro h
    refine ⟨sectionMap i b₀, section_mem_piece p sectionMap hproj i b₀, ?_⟩
    change JoinedIn (p ⁻¹' {p (sectionMap i b₀)})
      (sectionMap j (p (sectionMap i b₀))) (sectionMap i b₀)
    rw [hproj]
    exact h.symm

variable [Finite J]
  (hcover : ∀ x, ∃ j, JoinedIn (p ⁻¹' {p x}) x (sectionMap j (p x)))

include hcover in
omit [T2Space X] [PathConnectedSpace B] [Finite J] in
theorem cover : ∀ x, ∃ j, x ∈ piece p sectionMap j := by
  intro x
  obtain ⟨j, hj⟩ := hcover x
  exact ⟨j, hj.symm⟩

include hsource hfirst hp hproj hcover in
theorem joinedIn_iff_sample_reachable (b₀ : B) {i j : J} {x y : X}
    (hx : x ∈ piece p sectionMap i) (hy : y ∈ piece p sectionMap j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (SampleEdge p sectionMap b₀) i j := by
  have heq : ClosedPathCover.Overlap (piece p sectionMap) = SampleEdge p sectionMap b₀ := by
    funext i j
    exact propext (overlap_iff_sample p sectionMap chart hsource hfirst hp hproj b₀ i j)
  rw [ClosedPathCover.joinedIn_iff_reachable (piece p sectionMap)
    (fun i => (isClopen_piece p sectionMap chart hsource hfirst hp hproj i).isClosed)
    (cover p sectionMap hcover) (paths p sectionMap chart hsource hfirst hp hproj) hx hy, heq]

include hsource hfirst hp hproj hcover in
theorem isPreconnected_iff_sample_reachable (b₀ : B) :
    IsPreconnected (univ : Set X) ↔
      ∀ i j, Relation.ReflTransGen (SampleEdge p sectionMap b₀) i j := by
  have heq : ClosedPathCover.Overlap (piece p sectionMap) = SampleEdge p sectionMap b₀ := by
    funext i j
    exact propext (overlap_iff_sample p sectionMap chart hsource hfirst hp hproj b₀ i j)
  rw [ClosedPathCover.isPreconnected_iff_reachable (piece p sectionMap)
    (fun i => (isClopen_piece p sectionMap chart hsource hfirst hp hproj i).isClosed)
    (cover p sectionMap hcover) (paths p sectionMap chart hsource hfirst hp hproj), heq]
  constructor
  · intro h i j
    exact h i j ⟨_, section_mem_piece p sectionMap hproj i b₀⟩
      ⟨_, section_mem_piece p sectionMap hproj j b₀⟩
  · intro h i j _ _
    exact h i j

end Geometry
end LeanCanny.Connectivity.FiberSectionCover
