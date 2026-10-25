/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LocalProductBaseChange

/-! # Component transport over regular-value regions of proper smooth maps

Implicit-function charts construct the local products. They are pulled back
to the chosen parameter region, so critical values outside that region cause
no restriction. Two continuous sections are in the same fiber component at
one parameter precisely when they are at every parameter in a preconnected
regular-value region. The proof requires no global trivialization or ODE.
-/

@[expose] public section

namespace LeanCanny.Geometry.RegularComponentTransport
open Set Topology

section Subtype
variable {X B : Type*} [TopologicalSpace X] [TopologicalSpace B]

omit [TopologicalSpace B] in
/-- Paths in a restricted fiber are exactly paths in the original fiber. -/
theorem joinedIn_restrictPreimage_iff (f : X → B) (S : Set B) (b : S)
    (x y : f ⁻¹' S) (hx : S.restrictPreimage f x = b) (hy : S.restrictPreimage f y = b) :
    JoinedIn ((S.restrictPreimage f) ⁻¹' {b}) x y ↔
      JoinedIn (f ⁻¹' {b.val}) x.val y.val := by
  have himage : Subtype.val '' ((S.restrictPreimage f) ⁻¹' {b}) = f ⁻¹' {b.val} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact congrArg Subtype.val hw
    · intro hz
      have hzS : f z ∈ S := by rw [show f z = b.val from hz]; exact b.property
      refine ⟨⟨z, hzS⟩, ?_, rfl⟩
      exact Subtype.ext hz
  have hind : IsInducing (Subtype.val : f ⁻¹' S → X) := IsEmbedding.subtypeVal.isInducing
  have hx' : x ∈ (S.restrictPreimage f) ⁻¹' {b} := hx
  have hy' : y ∈ (S.restrictPreimage f) ⁻¹' {b} := hy
  have he := hind.joinedIn_image (F := (S.restrictPreimage f) ⁻¹' {b}) (x := x) (y := y) hx' hy'
  rw [himage] at he
  exact he.symm

end Subtype

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Construct the restricted implicit-chart family on a regular-value region. -/
theorem exists_charts (f : E → F) (S : Set F)
    (hf : ∀ x, f x ∈ S → ContDiffAt ℝ 1 f x)
    (hregular : ∀ x, f x ∈ S → Function.Surjective (fderiv ℝ f x)) :
    ∃ chart : ∀ x : f ⁻¹' S, OpenPartialHomeomorph (f ⁻¹' S) (S × (fderiv ℝ f x.val).ker),
      (∀ x, x ∈ (chart x).source) ∧
        ∀ a x, x ∈ (chart a).source → (chart a x).1 = S.restrictPreimage f x := by
  classical
  let p := S.restrictPreimage f
  have hchart (x : f ⁻¹' S) :
      ∃ chart : OpenPartialHomeomorph (f ⁻¹' S) (S × (fderiv ℝ f x.val).ker),
        x ∈ chart.source ∧ ∀ y ∈ chart.source, (chart y).1 = p y := by
    let D := fderiv ℝ f x.val
    have hder := (hf x.val x.property).hasStrictFDerivAt one_ne_zero
    have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr (hregular x.val x.property)
    let e := hder.implicitToOpenPartialHomeomorph f D hrange
    exact LocalProductFibers.exists_restricted_chart f S e x
      (hder.mem_implicitToOpenPartialHomeomorph_source hrange)
      (fun _ _ => hder.implicitToOpenPartialHomeomorph_fst _ _)
  choose chart hsource hfirst using hchart
  exact ⟨chart, hsource, hfirst⟩

/-- Connection to a moving endpoint is clopen. The parameter space need not
be connected; in particular it may be the original total slab. -/
theorem isClopen_joined_along (f : E → F) (S : Set F) (hp : IsProperMap f)
    (hf : ∀ x, f x ∈ S → ContDiffAt ℝ 1 f x)
    (hregular : ∀ x, f x ∈ S → Function.Surjective (fderiv ℝ f x))
    {A : Type*} [TopologicalSpace A] {base : A → S} {s d : A → E}
    (hbase : Continuous base) (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, f (s b) = (base b).val) (hpd : ∀ b, f (d b) = (base b).val) :
    IsClopen {b | JoinedIn (f ⁻¹' {(base b).val}) (s b) (d b)} := by
  obtain ⟨chart, hsource, hfirst⟩ := exists_charts f S hf hregular
  let p := S.restrictPreimage f
  have hsmem (c : A) : f (s c) ∈ S := by rw [hps c]; exact (base c).property
  have hdmem (c : A) : f (d c) ∈ S := by rw [hpd c]; exact (base c).property
  let s' : A → f ⁻¹' S := fun c => ⟨s c, hsmem c⟩
  let d' : A → f ⁻¹' S := fun c => ⟨d c, hdmem c⟩
  have hs' : Continuous s' := hs.subtype_mk _
  have hd' : Continuous d' := hd.subtype_mk _
  have hps' (c : A) : p (s' c) = base c := Subtype.ext (hps c)
  have hpd' (c : A) : p (d' c) = base c := Subtype.ext (hpd c)
  have h := LocalProductFibers.isClopen_joined_along p chart hsource hfirst
    (hp.restrictPreimage S) hbase hs' hd' hps' hpd'
  have heq : {a | JoinedIn (p ⁻¹' {base a}) (s' a) (d' a)} =
      {a | JoinedIn (f ⁻¹' {(base a).val}) (s a) (d a)} := by
    ext a
    exact joinedIn_restrictPreimage_iff f S (base a) (s' a) (d' a) (hps' a) (hpd' a)
  rwa [heq] at h

/-- This is the analytic transport theorem for the original map. The charts,
slice cover, openness, and local path connectivity are constructed internally. -/
theorem joined_sections_iff (f : E → F) (S : Set F) [PreconnectedSpace S]
    (hp : IsProperMap f)
    (hf : ∀ x, f x ∈ S → ContDiffAt ℝ 1 f x)
    (hregular : ∀ x, f x ∈ S → Function.Surjective (fderiv ℝ f x))
    {s d : S → E} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ b, f (s b) = b.val) (hpd : ∀ b, f (d b) = b.val) (a b : S) :
    JoinedIn (f ⁻¹' {a.val}) (s a) (d a) ↔ JoinedIn (f ⁻¹' {b.val}) (s b) (d b) := by
  have hcl := isClopen_joined_along f S hp hf hregular continuous_id hs hd hps hpd
  constructor
  · intro ha
    exact (isPreconnected_univ.subset_isClopen hcl ⟨a, mem_univ a, ha⟩) (mem_univ b)
  · intro hb
    exact (isPreconnected_univ.subset_isClopen hcl ⟨b, mem_univ b, hb⟩) (mem_univ a)

end LeanCanny.Geometry.RegularComponentTransport
