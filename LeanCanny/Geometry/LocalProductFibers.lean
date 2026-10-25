/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularFiber
public import LeanCanny.Geometry.FiberPathSeparation

/-! # Component transport from actual local product charts

Local charts whose first coordinate is the fiber map provide both openness of
the map and an open cover with path-connected slices. Restricting those same
charts to a fiber proves local path connectivity. For proper maps, the two
persistence theorems then make connection between continuous sections constant
over a preconnected base. No global trivialization or path-lifting oracle is
assumed.
-/

@[expose] public section

namespace LeanCanny.Geometry.LocalProductFibers
open Set Filter Topology
open scoped Topology

section OneChart
variable {X B G : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace G]
  [LocallyPathConnectedSpace G]

/-- A local product chart yields a neighborhood with connected slices. -/
theorem exists_slice_neighborhood (p : X → B) (e : OpenPartialHomeomorph X (B × G))
    {a : X} (ha : a ∈ e.source) (hfirst : ∀ x ∈ e.source, (e x).1 = p x) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∀ b, ∀ x ∈ U, p x = b →
      ∀ y ∈ U, p y = b → JoinedIn (p ⁻¹' {b}) x y := by
  obtain ⟨V, W, hV, hW, haV, haW, hVW⟩ :=
    isOpen_prod_iff.mp e.open_target (e a).1 (e a).2 (e.map_source ha)
  obtain ⟨Z, ⟨hZ, haZ, hpath⟩, hZW⟩ :=
    (isOpen_isPathConnected_basis (e a).2).mem_iff.mp (hW.mem_nhds haW)
  let U := e.source ∩ e ⁻¹' (V ×ˢ Z)
  have hVZ : V ×ˢ Z ⊆ e.target := (prod_mono Subset.rfl hZW).trans hVW
  refine ⟨U, e.isOpen_inter_preimage (hV.prod hZ), ⟨ha, haV, haZ⟩, ?_⟩
  intro b x hx hpx y hy hpy
  have hxb : (e x).1 = b := (hfirst x hx.1).trans hpx
  have hyb : (e y).1 = b := (hfirst y hy.1).trans hpy
  have hbV : b ∈ V := hxb ▸ hx.2.1
  let inv : G → X := fun z => e.symm (b, z)
  have hcont : ContinuousOn inv Z := e.symm.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun z hz => hVZ ⟨hbV, hz⟩)
  have hsub : inv '' Z ⊆ p ⁻¹' {b} := by
    rintro z ⟨w, hw, rfl⟩
    have htarget : (b, w) ∈ e.target := hVZ ⟨hbV, hw⟩
    exact (hfirst _ (e.map_target htarget)).symm.trans (congrArg Prod.fst (e.right_inv htarget))
  have hxI : x ∈ inv '' Z := by
    refine ⟨(e x).2, hx.2.2, ?_⟩
    change e.symm (b, (e x).2) = x
    rw [show (b, (e x).2) = e x from Prod.ext hxb.symm rfl, e.left_inv hx.1]
  have hyI : y ∈ inv '' Z := by
    refine ⟨(e y).2, hy.2.2, ?_⟩
    change e.symm (b, (e y).2) = y
    rw [show (b, (e y).2) = e y from Prod.ext hyb.symm rfl, e.left_inv hy.1]
  exact ((hpath.image' hcont).joinedIn x hxI y hyI).mono hsub

end OneChart

section Atlas
variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]
  (p : X → B) {G : X → Type*} [∀ x, TopologicalSpace (G x)]
  (chart : ∀ x, OpenPartialHomeomorph X (B × G x))
  (hsource : ∀ x, x ∈ (chart x).source)
  (hfirst : ∀ a x, x ∈ (chart a).source → (chart a x).1 = p x)

include hsource hfirst in
/-- A map with local product charts is open. -/
theorem isOpenMap : IsOpenMap p := by
  intro U hU
  have heq : p '' U = ⋃ x : U, Prod.fst '' ((chart x.val) '' ((chart x.val).source ∩ U)) := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, chart x x, ⟨x, ⟨hsource x, hx⟩, rfl⟩, hfirst x x (hsource x)⟩
    · intro hb
      obtain ⟨x, z, ⟨y, hy, rfl⟩, hz⟩ := mem_iUnion.mp hb
      exact ⟨y, hy.2, (hfirst x.val y hy.1).symm.trans hz⟩
  rw [heq]
  exact isOpen_iUnion (fun x => isOpenMap_fst _ ((chart x.val).isOpen_image_source_inter hU))

variable [∀ x, LocallyPathConnectedSpace (G x)]

include hsource hfirst in
/-- The slice cover is constructed from the charts, rather than assumed. -/
theorem exists_slice_cover : ∃ box : X → Set X,
    (∀ i, IsOpen (box i)) ∧ (∀ x, x ∈ box x) ∧
      ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b → JoinedIn (p ⁻¹' {b}) x y := by
  choose box hopen hmem hpaths using fun x =>
    exists_slice_neighborhood p (chart x) (hsource x) (hfirst x)
  exact ⟨box, hopen, hmem, fun b i => hpaths i b⟩

include hsource hfirst in
theorem locallyPathConnected_fiber (b : B) : LocallyPathConnectedSpace (p ⁻¹' {b}) := by
  let charts (x : p ⁻¹' {b}) := RegularFiber.restrictFiber (chart x.val) p b x (hfirst x.val)
  exact RegularFiber.locallyPathConnected_of_charts charts (fun x => hsource x.val)

variable [T2Space X]

include hsource hfirst in
/-- Fiber connection remains clopen for arbitrary continuous moving endpoints. -/
theorem isClopen_joined_along {A : Type*} [TopologicalSpace A] (hp : IsProperMap p)
    {base : A → B} {s d : A → X} (hbase : Continuous base)
    (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = base b) (hpd : ∀ b, p (d b) = base b) :
    IsClopen {b | JoinedIn (p ⁻¹' {base b}) (s b) (d b)} := by
  let : ∀ b, LocallyPathConnectedSpace (p ⁻¹' {b}) :=
    locallyPathConnected_fiber p chart hsource hfirst
  obtain ⟨box, hopen, hmem, hpaths⟩ := exists_slice_cover p chart hsource hfirst
  exact FiberPathPersistence.isClopen_joined_along p box hp (isOpenMap p chart hsource hfirst)
    hopen (fun x => ⟨x, hmem x⟩) hpaths hbase hs hd hps hpd

include hsource hfirst in
/-- Proper local product charts suffice for fiber component transport between
continuous sections. No global product structure is required. -/
theorem joined_sections_iff [PreconnectedSpace B] (hp : IsProperMap p)
    {s d : B → X} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = b) (hpd : ∀ b, p (d b) = b) (a b : B) :
    JoinedIn (p ⁻¹' {a}) (s a) (d a) ↔ JoinedIn (p ⁻¹' {b}) (s b) (d b) := by
  let : ∀ b, LocallyPathConnectedSpace (p ⁻¹' {b}) :=
    locallyPathConnected_fiber p chart hsource hfirst
  obtain ⟨box, hopen, hmem, hpaths⟩ := exists_slice_cover p chart hsource hfirst
  exact FiberPathPersistence.joined_sections_iff p box hp (isOpenMap p chart hsource hfirst)
    hopen (fun x => ⟨x, hmem x⟩) hpaths hs hd hps hpd a b

end Atlas
end LeanCanny.Geometry.LocalProductFibers
