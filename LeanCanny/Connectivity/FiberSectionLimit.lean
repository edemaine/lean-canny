/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FiberSectionCover
public import LeanCanny.Connectivity.EndpointAttachment
public import LeanCanny.Geometry.ConnectedSlabLimit
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.LocalAtTarget

/-! # Endpoint limits of transported fiber components

The saturated pieces of a regular slab have path-connected short tails.
Their entire endpoint limits are therefore compact and connected, including
at singular levels where the local product charts no longer apply.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FiberSectionCover
open Set Geometry

variable {X J : Type*} [TopologicalSpace X] [T2Space X]
  (p : X → ℝ) {a b : ℝ}
  (sectionMap : J → C(Ioo a b, p ⁻¹' Ioo a b))

/-- The original ambient subset, so its closure includes critical endpoints. -/
def ambientPiece (j : J) : Set X :=
  Subtype.val '' piece ((Ioo a b).restrictPreimage p) sectionMap j

variable {G : p ⁻¹' Ioo a b → Type*} [∀ x, TopologicalSpace (G x)]
  [∀ x, LocallyPathConnectedSpace (G x)]
  (chart : ∀ x, OpenPartialHomeomorph (p ⁻¹' Ioo a b) (Ioo a b × G x))
  (hsource : ∀ x, x ∈ (chart x).source)
  (hfirst : ∀ z x, x ∈ (chart z).source → (chart z x).1 = (Ioo a b).restrictPreimage p x)
  (hp : IsProperMap p)
  (hproj : ∀ j t, (Ioo a b).restrictPreimage p (sectionMap j t) = t)

include hsource hfirst hp hproj in
theorem isPathConnected_ambient_restrict (j : J) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ Ioo a b) :
    IsPathConnected (ambientPiece p sectionMap j ∩ p ⁻¹' Ioo c d) := by
  let U : Set (Ioo a b) := Subtype.val ⁻¹' Ioo c d
  have hU : IsPathConnected U := by
    apply (Topology.IsEmbedding.subtypeVal.isInducing.isPathConnected_iff).mpr
    have he : Subtype.val '' U = Ioo c d := by
      ext t
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro ht
        exact ⟨⟨t, hsub ht⟩, ht, rfl⟩
    rw [he]
    exact (convex_Ioo c d).isPathConnected ⟨(c + d) / 2, by constructor <;> linarith⟩
  have hpaths := isPathConnected_piece_preimage ((Ioo a b).restrictPreimage p)
    sectionMap chart hsource hfirst (hp.restrictPreimage (Ioo a b)) hproj j hU
  have he : ambientPiece p sectionMap j ∩ p ⁻¹' Ioo c d =
      Subtype.val '' (piece ((Ioo a b).restrictPreimage p) sectionMap j ∩
        ((Ioo a b).restrictPreimage p) ⁻¹' U) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      exact ⟨z, ⟨hz, hx⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hx⟩
  rw [he]
  exact hpaths.image continuous_subtype_val

include hsource hfirst hp hproj in
theorem isPathConnected_ambient_tail (j : J) (c : Ioo a b) :
    IsPathConnected (ConnectedSlabLimit.tail p (a := a) (ambientPiece p sectionMap j) c.val) :=
  isPathConnected_ambient_restrict p sectionMap chart hsource hfirst hp hproj j c.property.1
    (fun _ h => ⟨h.1, h.2.trans c.property.2⟩)

include hsource hfirst hp hproj in
/-- All limit points of a transported component lie in one connected subset
of the endpoint fiber. The endpoint itself need not be regular. -/
theorem isConnected_ambient_endpoint (hab : a < b) (j : J) :
    IsConnected (closure (ambientPiece p sectionMap j) ∩ p ⁻¹' {a}) := by
  apply ConnectedSlabLimit.isConnected_endpoint p hp hab ?_
    (fun c => (isPathConnected_ambient_tail p sectionMap chart hsource hfirst hp hproj j c).isConnected)
  rintro x ⟨z, _, rfl⟩
  exact z.property

include hsource hfirst hp hproj in
theorem isConnected_ambient_endpoint_right (hab : a < b) (j : J) :
    IsConnected (closure (ambientPiece p sectionMap j) ∩ p ⁻¹' {b}) := by
  apply ConnectedSlabLimit.isConnected_endpoint_right p hp hab ?_
    (fun c => (isPathConnected_ambient_restrict p sectionMap chart hsource hfirst hp hproj j
      c.property.2 (fun _ h => ⟨c.property.1.trans h.1, h.2⟩)).isConnected)
  rintro x ⟨z, _, rfl⟩
  exact z.property

include hsource hfirst hp hproj in
/-- A continuous extension of the indexing section attaches every ambient
limit point of its full saturated component through a recursive slice cover. -/
theorem joinedIn_ambient_endpoint {I : Type*} [Finite I]
    (slice : I → Set (p ⁻¹' {a})) (hcover : ∀ x, ∃ i, x ∈ slice i)
    (haccess : ∀ i, FrontierCover.Accessible (slice i)) (hab : a < b) (j : J)
    (arc : ℝ → X) (hc : ContinuousOn arc (Icc a b)) (hlevel : p (arc a) = a)
    (hmatch : ∀ t : Ioo a b, (sectionMap j t).val = arc t.val)
    {x : X} (hx : x ∈ closure (ambientPiece p sectionMap j)) (hpx : p x = a) (t : Ioo a b) :
    JoinedIn (p ⁻¹' {a} ∪ ambientPiece p sectionMap j) x (arc t.val) := by
  apply EndpointAttachment.joinedIn_curve p slice hcover haccess hp hab ?_
    (fun c => (isPathConnected_ambient_tail p sectionMap chart hsource hfirst hp hproj j c).isConnected.isPreconnected)
    arc hc hlevel ?_ hx hpx t
  · rintro z ⟨w, _, rfl⟩
    exact w.property
  · rintro z ⟨u, hu, rfl⟩
    exact ⟨sectionMap j ⟨u, hu⟩, section_mem_piece _ sectionMap hproj j ⟨u, hu⟩, hmatch ⟨u, hu⟩⟩

include hsource hfirst hp hproj in
/-- Every incidence of a full slab component with a recursive slice piece
is represented by a finite slice-graph walk to its critical-branch endpoint.
The slice pieces need not be closed or accessible for this forward direction. -/
theorem endpoint_incidence_reachable {I : Type*} [Finite I]
    (slice : I → Set (p ⁻¹' {a})) (hcover : ∀ x, ∃ i, x ∈ slice i)
    (hab : a < b) (j : J) (arc : ℝ → X) (hc : ContinuousOn arc (Icc a b))
    (hlevel : p (arc a) = a) (hmatch : ∀ t : Ioo a b, (sectionMap j t).val = arc t.val)
    {x : p ⁻¹' {a}} {i : I} (hx : x.val ∈ closure (ambientPiece p sectionMap j))
    (hxi : x ∈ slice i) :
    ∃ k, (⟨arc a, hlevel⟩ : p ⁻¹' {a}) ∈ slice k ∧
      Relation.ReflTransGen (FrontierCover.Incident slice) i k := by
  have ha : a ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩
  have hz : arc a ∈ closure (arc '' Ioo a b) :=
    ((hc a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self).mem_closure_image ha
  have hsub : arc '' Ioo a b ⊆ ambientPiece p sectionMap j := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨sectionMap j ⟨u, hu⟩, section_mem_piece _ sectionMap hproj j ⟨u, hu⟩, hmatch ⟨u, hu⟩⟩
  obtain ⟨k, hk⟩ := hcover ⟨arc a, hlevel⟩
  refine ⟨k, hk, ?_⟩
  apply EndpointAttachment.reachable_endpoint p slice hcover hp hab ?_
    (fun c => (isPathConnected_ambient_tail p sectionMap chart hsource hfirst hp hproj j c).isConnected.isPreconnected)
    hx (closure_mono hsub hz) hxi hk
  rintro z ⟨w, _, rfl⟩
  exact w.property

end LeanCanny.Connectivity.FiberSectionCover
