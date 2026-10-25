/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OpenPathCover

/-! # Persistence of paths between sections of a fiber map

Suppose an open map has an open cover whose slices are path connected.
An existing fiber path passes through a finite chain of overlapping pieces.
Each overlap persists on a parameter neighborhood because the map is open.
Continuous sections stay in their endpoint pieces, so their fiber connection
is an open condition on the parameter. Neither compactness nor a finite cover
is required for this direction of component transport.
-/

@[expose] public section

namespace LeanCanny.Geometry.FiberPathPersistence
open Set Filter
open LeanCanny.Connectivity
open scoped Topology

variable {X B ι : Type*} [TopologicalSpace X] [TopologicalSpace B]
  (p : X → B) (box : ι → Set X)

def Edge (b : B) (i j : ι) : Prop :=
  ∃ x, p x = b ∧ x ∈ box i ∧ x ∈ box j

private def piece (b : B) (i : ι) : Set (p ⁻¹' {b}) := Subtype.val ⁻¹' box i

omit [TopologicalSpace X] [TopologicalSpace B] in
private theorem overlap_iff (b : B) (i j : ι) :
    ClosedPathCover.Overlap (piece p box b) i j ↔ Edge p box b i j := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x.val, x.property, hx, hy⟩
  · rintro ⟨x, hx, hi, hj⟩
    exact ⟨⟨x, hx⟩, hi, hj⟩

omit [TopologicalSpace B] in
/-- An existing fiber path gives a finite chain in the open slice cover. -/
theorem walk_of_joinedIn (hopen : ∀ i, IsOpen (box i)) (hcover : ∀ x, ∃ i, x ∈ box i)
    {b : B} {i j : ι} {x y : X} (hx : x ∈ box i) (hy : y ∈ box j)
    (h : JoinedIn (p ⁻¹' {b}) x y) : Relation.ReflTransGen (Edge p box b) i j := by
  let x' : p ⁻¹' {b} := ⟨x, h.source_mem⟩
  let y' : p ⁻¹' {b} := ⟨y, h.target_mem⟩
  have hr := OpenPathCover.reachable_of_joinedIn (piece p box b)
    (fun i => (hopen i).preimage continuous_subtype_val)
    (fun z => hcover z.val) (x := x') (y := y') hx hy (joinedIn_univ.mpr h.joined_subtype)
  exact hr.lift id (fun _ _ he => (overlap_iff p box b _ _).mp he)

omit [TopologicalSpace B] in
/-- Slice paths turn such a chain into a fiber path. -/
theorem joinedIn_of_walk
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {b : B} {i j : ι} {x y : X} (hx : x ∈ box i) (hpx : p x = b)
    (hy : y ∈ box j) (hpy : p y = b) (h : Relation.ReflTransGen (Edge p box b) i j) :
    JoinedIn (p ⁻¹' {b}) x y := by
  induction h generalizing y with
  | refl => exact hpaths b _ x hx hpx y hy hpy
  | @tail j k hr he ih =>
    obtain ⟨z, hpz, hzj, hzk⟩ := he
    exact (ih hzj hpz).trans (hpaths b k z hzk hpz y hy hpy)

theorem isOpen_edge (hp : IsOpenMap p) (hopen : ∀ i, IsOpen (box i)) (i j : ι) :
    IsOpen {b | Edge p box b i j} := by
  have heq : {b | Edge p box b i j} = p '' (box i ∩ box j) := by
    ext b
    simp only [Edge, mem_ofPred_eq, mem_image, mem_inter_iff]
    constructor
    · rintro ⟨x, hx, hi, hj⟩
      exact ⟨x, ⟨hi, hj⟩, hx⟩
    · rintro ⟨x, ⟨hi, hj⟩, hx⟩
      exact ⟨x, hx, hi, hj⟩
  rw [heq]
  exact hp _ ((hopen i).inter (hopen j))

/-- A finite walk survives on one common parameter neighborhood. -/
theorem eventually_walk (hp : IsOpenMap p) (hopen : ∀ i, IsOpen (box i))
    {b : B} {i j : ι} (h : Relation.ReflTransGen (Edge p box b) i j) :
    ∀ᶠ c in 𝓝 b, Relation.ReflTransGen (Edge p box c) i j := by
  induction h with
  | refl => exact Eventually.of_forall (fun _ => .refl)
  | @tail j k hr he ih =>
    filter_upwards [ih, (isOpen_edge p box hp hopen j k).mem_nhds he] with c hc he
    exact hc.tail he

/-- Fiber connection is open for any continuous family of pairs of endpoints,
including when the parameter is a moving point of the total space. -/
theorem isOpen_joined_along {A : Type*} [TopologicalSpace A]
    (hp : IsOpenMap p) (hopen : ∀ i, IsOpen (box i))
    (hcover : ∀ x, ∃ i, x ∈ box i)
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {base : A → B} {s d : A → X} (hbase : Continuous base)
    (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = base b) (hpd : ∀ b, p (d b) = base b) :
    IsOpen {b | JoinedIn (p ⁻¹' {base b}) (s b) (d b)} := by
  rw [isOpen_iff_mem_nhds]
  intro b hb
  obtain ⟨i, hi⟩ := hcover (s b)
  obtain ⟨j, hj⟩ := hcover (d b)
  have hwalk := walk_of_joinedIn p box hopen hcover hi hj hb
  have hsi : ∀ᶠ c in 𝓝 b, s c ∈ box i := hs.continuousAt.preimage_mem_nhds ((hopen i).mem_nhds hi)
  have hdj : ∀ᶠ c in 𝓝 b, d c ∈ box j := hd.continuousAt.preimage_mem_nhds ((hopen j).mem_nhds hj)
  have hwalk' := hbase.continuousAt.eventually (eventually_walk p box hp hopen hwalk)
  filter_upwards [hwalk', hsi, hdj] with c hc hsc hdc
  exact joinedIn_of_walk p box hpaths hsc (hps c) hdc (hpd c) hc

/-- Connection of continuous sections within their fibers is open in the
parameter. The cover and its slice paths must be established geometrically. -/
theorem isOpen_joined_sections (hp : IsOpenMap p) (hopen : ∀ i, IsOpen (box i))
    (hcover : ∀ x, ∃ i, x ∈ box i)
    (hpaths : ∀ b i, ∀ x ∈ box i, p x = b → ∀ y ∈ box i, p y = b →
      JoinedIn (p ⁻¹' {b}) x y)
    {s d : B → X} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, p (s b) = b) (hpd : ∀ b, p (d b) = b) :
    IsOpen {b | JoinedIn (p ⁻¹' {b}) (s b) (d b)} :=
  isOpen_joined_along p box hp hopen hcover hpaths continuous_id hs hd hps hpd

end LeanCanny.Geometry.FiberPathPersistence
