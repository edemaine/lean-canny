/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FiberPathPersistence
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-! # Persistence of separation in proper fiber families

In a compact locally path-connected fiber, a component and its complement are
disjoint compact sets. Disjoint ambient neighborhoods separate them. Closedness
of the proper projection keeps nearby fibers in those neighborhoods, so a path
cannot newly cross between them. Together with path persistence this makes
connection between continuous sections constant over a connected parameter
region. The hypotheses on local slice neighborhoods are still explicit here.
-/

@[expose] public section

namespace LeanCanny.Geometry.FiberPathPersistence
open Set Filter
open scoped Topology

variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [T2Space X]
  (p : X → B)

/-- Fiber connection is closed for arbitrary continuously varying endpoint
pairs of a proper map with locally path-connected fibers. -/
theorem isClosed_joined_along {A : Type*} [TopologicalSpace A] (hp : IsProperMap p)
    [∀ b, LocallyPathConnectedSpace (p ⁻¹' {b})]
    {base : A → B} {s d : A → X} (hbase : Continuous base)
    (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = base b) (hpd : ∀ b, p (d b) = base b) :
    IsClosed {b | JoinedIn (p ⁻¹' {base b}) (s b) (d b)} := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro b hb
  change ¬ JoinedIn (p ⁻¹' {base b}) (s b) (d b) at hb
  let K := p ⁻¹' {base b}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (hp.isCompact_preimage isCompact_singleton)
  let x : K := ⟨s b, hps b⟩
  let y : K := ⟨d b, hpd b⟩
  let C : Set K := connectedComponent x
  have hy : y ∉ C := by
    intro hy
    have hj : Joined x y := by
      apply mem_pathComponent_iff.mp
      rwa [pathComponent_eq_connectedComponent]
    exact hb ((joinedIn_iff_joined (hps b) (hpd b)).mpr hj)
  have hC : IsCompact C := isClosed_connectedComponent.isCompact
  have hD : IsCompact Cᶜ := isOpen_connectedComponent.isClosed_compl.isCompact
  have hdis : Disjoint (Subtype.val '' C) (Subtype.val '' Cᶜ) := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, rfl⟩ ⟨w, hw, hwa⟩
    have heq : w = a := Subtype.ext hwa
    have hn : a ∉ C := by simpa only [heq, mem_compl_iff] using hw
    exact hn ha
  obtain ⟨U, V, hU, hV, hCU, hDV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hC.image continuous_subtype_val) (hD.image continuous_subtype_val) hdis
  have hsU : s b ∈ U := hCU ⟨x, mem_connectedComponent, rfl⟩
  have hdV : d b ∈ V := hDV ⟨y, hy, rfl⟩
  have hcover : ∀ z ∈ p ⁻¹' {base b}, z ∈ U ∪ V := by
    intro z hz
    let w : K := ⟨z, hz⟩
    by_cases hw : w ∈ C
    · exact Or.inl (hCU ⟨w, hw, rfl⟩)
    · exact Or.inr (hDV ⟨w, hw, rfl⟩)
  have hfib : ∀ᶠ c in 𝓝 (base b), ∀ z ∈ p ⁻¹' {c}, z ∈ U ∪ V :=
    hp.isClosedMap.eventually_nhds_fiber (base b) (fun z hz => (hU.union hV).mem_nhds (hcover z hz))
  have hsu : ∀ᶠ c in 𝓝 b, s c ∈ U := hs.continuousAt.preimage_mem_nhds (hU.mem_nhds hsU)
  have hdv : ∀ᶠ c in 𝓝 b, d c ∈ V := hd.continuousAt.preimage_mem_nhds (hV.mem_nhds hdV)
  filter_upwards [hbase.continuousAt.eventually hfib, hsu, hdv] with c hc hsc hdc
  change ¬ JoinedIn (p ⁻¹' {base c}) (s c) (d c)
  rintro ⟨γ, hγ⟩
  have hsub : range γ ⊆ U ∪ V := by
    rintro z ⟨t, rfl⟩
    exact hc _ (hγ t)
  have hleft := (isPreconnected_range γ.continuous).subset_left_of_subset_union hU hV hUV hsub
    ⟨s c, γ.source_mem_range, hsc⟩
  exact Set.disjoint_left.mp hUV (hleft γ.target_mem_range) hdc

/-- Fiber connection of continuous sections is closed for a proper map with
locally path-connected fibers. No differentiability assumption is needed. -/
theorem isClosed_joined_sections (hp : IsProperMap p)
    [∀ b, LocallyPathConnectedSpace (p ⁻¹' {b})]
    {s d : B → X} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = b) (hpd : ∀ b, p (d b) = b) :
    IsClosed {b | JoinedIn (p ⁻¹' {b}) (s b) (d b)} :=
  isClosed_joined_along p hp continuous_id hs hd hps hpd

/-- The general endpoint relation is clopen when local slice paths persist. -/
theorem isClopen_joined_along {A ι : Type*} [TopologicalSpace A] (box : ι → Set X)
    (hp : IsProperMap p) (hpo : IsOpenMap p)
    [∀ b, LocallyPathConnectedSpace (p ⁻¹' {b})]
    (hopen : ∀ i, IsOpen (box i)) (hcover : ∀ x, ∃ i, x ∈ box i)
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {base : A → B} {s d : A → X} (hbase : Continuous base)
    (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = base b) (hpd : ∀ b, p (d b) = base b) :
    IsClopen {b | JoinedIn (p ⁻¹' {base b}) (s b) (d b)} :=
  ⟨isClosed_joined_along p hp hbase hs hd hps hpd,
    isOpen_joined_along p box hpo hopen hcover hpaths hbase hs hd hps hpd⟩

/-- The two persistence directions give a clopen fiber-connection predicate. -/
theorem isClopen_joined_sections {ι : Type*} (box : ι → Set X)
    (hp : IsProperMap p) (hpo : IsOpenMap p)
    [∀ b, LocallyPathConnectedSpace (p ⁻¹' {b})]
    (hopen : ∀ i, IsOpen (box i)) (hcover : ∀ x, ∃ i, x ∈ box i)
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {s d : B → X} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = b) (hpd : ∀ b, p (d b) = b) :
    IsClopen {b | JoinedIn (p ⁻¹' {b}) (s b) (d b)} :=
  ⟨isClosed_joined_sections p hp hs hd hps hpd,
    isOpen_joined_sections p box hpo hopen hcover hpaths hs hd hps hpd⟩

/-- On a preconnected parameter space, one fiber decides whether two entire
continuous sections belong to the same fiber components everywhere. -/
theorem joined_sections_iff [PreconnectedSpace B] {ι : Type*} (box : ι → Set X)
    (hp : IsProperMap p) (hpo : IsOpenMap p)
    [∀ b, LocallyPathConnectedSpace (p ⁻¹' {b})]
    (hopen : ∀ i, IsOpen (box i)) (hcover : ∀ x, ∃ i, x ∈ box i)
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {s d : B → X} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = b) (hpd : ∀ b, p (d b) = b) (a b : B) :
    JoinedIn (p ⁻¹' {a}) (s a) (d a) ↔ JoinedIn (p ⁻¹' {b}) (s b) (d b) := by
  have hcl := isClopen_joined_sections p box hp hpo hopen hcover hpaths hs hd hps hpd
  constructor
  · intro ha
    exact (isPreconnected_univ.subset_isClopen hcl ⟨a, mem_univ a, ha⟩) (mem_univ b)
  · intro hb
    exact (isPreconnected_univ.subset_isClopen hcl ⟨b, mem_univ b, hb⟩) (mem_univ a)

end LeanCanny.Geometry.FiberPathPersistence
