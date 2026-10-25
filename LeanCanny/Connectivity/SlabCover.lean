/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ArcIncidence
public import Mathlib.Basic.Finite.Sum

/-! # Gluing regular arcs to endpoint-slice decompositions

A complete family of arcs on an open slab, together with accessible covers of
its two endpoint fibers, forms an accessible cover of the whole closed slab.
The finite frontier graph therefore preserves both paths and connectedness.
All closures and paths are relative to the described slab. The endpoint
pieces may be nonclosed, and the slab need not be a manifold at its endpoints.

Constructing the regular slabs and their effective descriptions for a general
semialgebraic input remains a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Connectivity.SlabCover
open Set

variable {E J L R : Type*} [TopologicalSpace E] [T2Space E]

abbrev Space (H : ℝ → E → Prop) (a b : ℝ) :=
  {z : ℝ × E // z.1 ∈ Icc a b ∧ H z.1 z.2}

/-- Arc vertices and the two recursively supplied slice-vertex families. -/
abbrev Index (J L R : Type*) := J ⊕ (L ⊕ R)

def ambientPiece (curve : J → ℝ → E) (left : L → Set E) (right : R → Set E)
    (a b : ℝ) : Index J L R → Set (ℝ × E) :=
  Sum.elim (fun j => (fun t => (t, curve j t)) '' Ioo a b)
    (Sum.elim (fun l => (fun x => (a, x)) '' left l)
      (fun r => (fun x => (b, x)) '' right r))

def piece (H : ℝ → E → Prop) (curve : J → ℝ → E)
    (left : L → Set E) (right : R → Set E) (a b : ℝ) :
    Index J L R → Set (Space H a b) := fun i =>
  Subtype.val ⁻¹' ambientPiece curve left right a b i

/-- The recursive input at a critical parameter value. -/
structure FiberCover (H : ℝ → E → Prop) (c : ℝ) (I : Type*) where
  piece : I → Set E
  subset : ∀ i x, x ∈ piece i → H c x
  cover : ∀ x, H c x → ∃ i, x ∈ piece i
  accessible : ∀ i, FrontierCover.Accessible (piece i)

section Decomposition
variable (H : ℝ → E → Prop) {a b : ℝ} (hab : a < b)
  (curve : J → ℝ → E)
  (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
  (hroot : ∀ j t, t ∈ Icc a b → H t (curve j t))
  (hcomplete : ∀ t ∈ Ioo a b, ∀ x, H t x → ∃ j, curve j t = x)
  (left : L → Set E) (right : R → Set E)
  (hlsub : ∀ l x, x ∈ left l → H a x) (hrsub : ∀ r x, x ∈ right r → H b x)
  (hlcover : ∀ x, H a x → ∃ l, x ∈ left l)
  (hrcover : ∀ x, H b x → ∃ r, x ∈ right r)
  (hlaccess : ∀ l, FrontierCover.Accessible (left l))
  (hraccess : ∀ r, FrontierCover.Accessible (right r))

include hab hroot hlsub hrsub in
omit [TopologicalSpace E] [T2Space E] in
theorem ambientPiece_subset (i : Index J L R) :
    ambientPiece curve left right a b i ⊆ {z | z.1 ∈ Icc a b ∧ H z.1 z.2} := by
  rcases i with j | (l | r)
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨Ioo_subset_Icc_self ht, hroot j t (Ioo_subset_Icc_self ht)⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨le_rfl, hab.le⟩, hlsub l x hx⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨hab.le, le_rfl⟩, hrsub r x hx⟩

include hcomplete hlcover hrcover in
omit [TopologicalSpace E] [T2Space E] in
theorem cover : ∀ z : Space H a b, ∃ i, z ∈ piece H curve left right a b i := by
  intro z
  rcases eq_or_lt_of_le z.property.1.1 with ha | ha
  · have hz : H a z.val.2 := by simpa only [← ha] using z.property.2
    obtain ⟨l, hl⟩ := hlcover z.val.2 hz
    exact ⟨.inr (.inl l), z.val.2, hl, Prod.ext ha rfl⟩
  · rcases eq_or_lt_of_le z.property.1.2 with hb | hb
    · have hz : H b z.val.2 := by simpa only [hb] using z.property.2
      obtain ⟨r, hr⟩ := hrcover z.val.2 hz
      exact ⟨.inr (.inr r), z.val.2, hr, Prod.ext hb.symm rfl⟩
    · obtain ⟨j, hj⟩ := hcomplete z.val.1 ⟨ha, hb⟩ z.val.2 z.property.2
      exact ⟨.inl j, z.val.1, ⟨ha, hb⟩, Prod.ext rfl hj⟩

include hab hc hroot hlsub hrsub hlaccess hraccess in
theorem accessible (i : Index J L R) :
    FrontierCover.Accessible (piece H curve left right a b i) := by
  have hsub := ambientPiece_subset H hab curve hroot left right hlsub hrsub i
  apply FrontierCover.Accessible.subtype (s := ambientPiece curve left right a b i) _ hsub
  rcases i with j | (l | r)
  · exact FrontierCover.accessible_open_arc (continuous_id.continuousOn.prodMk (hc j))
  · exact (hlaccess l).image (continuous_const.prodMk continuous_id) (isClosedMap_prodMk_left a)
  · exact (hraccess r).image (continuous_const.prodMk continuous_id) (isClosedMap_prodMk_left b)

include hab hroot hlsub hrsub in
omit [T2Space E] in
theorem incident_iff_ambient (i j : Index J L R) :
    FrontierCover.Incident (piece H curve left right a b) i j ↔
      FrontierCover.Incident (ambientPiece curve left right a b) i j := by
  apply FrontierCover.incident_preimage_iff _ Topology.IsEmbedding.subtypeVal
  intro k z hz
  exact ⟨⟨z, ambientPiece_subset H hab curve hroot left right hlsub hrsub k hz⟩, rfl⟩

include hab hc hroot hlsub hrsub in
theorem incident_arc_left_iff (j : J) (l : L) :
    FrontierCover.Incident (piece H curve left right a b) (.inl j) (.inr (.inl l)) ↔
      curve j a ∈ left l := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  change (( ((fun t => (t, curve j t)) '' Ioo a b) ∩
      closure ((fun x => (a, x)) '' left l)).Nonempty ∨
    (((fun x => (a, x)) '' left l) ∩
      closure ((fun t => (t, curve j t)) '' Ioo a b)).Nonempty) ↔ _
  rw [or_comm, FrontierCover.incident_graphArc_slice_iff hab (hc j)
    ⟨le_rfl, hab.le⟩ (by simp) (by rintro z ⟨x, _, rfl⟩; rfl)]
  simp only [mem_image, Prod.mk.injEq, true_and, exists_eq_right]

include hab hc hroot hlsub hrsub in
theorem incident_arc_right_iff (j : J) (r : R) :
    FrontierCover.Incident (piece H curve left right a b) (.inl j) (.inr (.inr r)) ↔
      curve j b ∈ right r := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  change (( ((fun t => (t, curve j t)) '' Ioo a b) ∩
      closure ((fun x => (b, x)) '' right r)).Nonempty ∨
    (((fun x => (b, x)) '' right r) ∩
      closure ((fun t => (t, curve j t)) '' Ioo a b)).Nonempty) ↔ _
  rw [or_comm, FrontierCover.incident_graphArc_slice_iff hab (hc j)
    ⟨hab.le, le_rfl⟩ (by simp) (by rintro z ⟨x, _, rfl⟩; rfl)]
  simp only [mem_image, Prod.mk.injEq, true_and, exists_eq_right]

include hab hc hroot hlsub hrsub in
theorem incident_arcs_iff
    (hinj : ∀ t ∈ Ioo a b, Function.Injective (fun j => curve j t)) (i j : J) :
    FrontierCover.Incident (piece H curve left right a b) (.inl i) (.inl j) ↔ i = j := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  exact FrontierCover.incident_graphArcs_iff hab curve hc hinj i j

include hab hroot hlsub hrsub in
omit [T2Space E] in
theorem incident_left_iff (i j : L) :
    FrontierCover.Incident (piece H curve left right a b) (.inr (.inl i)) (.inr (.inl j)) ↔
      FrontierCover.Incident left i j := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  exact FrontierCover.incident_slice_image_iff left a i j

include hab hroot hlsub hrsub in
omit [T2Space E] in
theorem incident_right_iff (i j : R) :
    FrontierCover.Incident (piece H curve left right a b) (.inr (.inr i)) (.inr (.inr j)) ↔
      FrontierCover.Incident right i j := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  exact FrontierCover.incident_slice_image_iff right b i j

include hab hroot hlsub hrsub in
omit [T2Space E] in
theorem not_incident_left_right (l : L) (r : R) :
    ¬ FrontierCover.Incident (piece H curve left right a b) (.inr (.inl l)) (.inr (.inr r)) := by
  rw [incident_iff_ambient H hab curve hroot left right hlsub hrsub]
  exact FrontierCover.not_incident_distinct_slices hab.ne
    (by rintro z ⟨x, _, rfl⟩; rfl) (by rintro z ⟨x, _, rfl⟩; rfl)

variable [Finite J] [Finite L] [Finite R]

include hab hc hroot hcomplete hlsub hrsub hlcover hrcover hlaccess hraccess in
/-- The slab's paths are exactly walks in the assembled finite frontier graph. -/
theorem joinedIn_iff_reachable {i j : Index J L R} {x y : Space H a b}
    (hx : x ∈ piece H curve left right a b i) (hy : y ∈ piece H curve left right a b j) :
    JoinedIn univ x y ↔
      Relation.ReflTransGen (FrontierCover.Incident (piece H curve left right a b)) i j :=
  FrontierCover.joinedIn_iff_reachable _ (cover H curve hcomplete left right hlcover hrcover)
    (accessible H hab curve hc hroot left right hlsub hrsub hlaccess hraccess) hx hy

include hab hc hroot hcomplete hlsub hrsub hlcover hrcover hlaccess hraccess in
/-- This also covers empty fibers and empty slabs without a nonemptiness axiom. -/
theorem isPreconnected_iff_reachable :
    IsPreconnected (univ : Set (Space H a b)) ↔
      ∀ i j, (piece H curve left right a b i).Nonempty →
        (piece H curve left right a b j).Nonempty →
        Relation.ReflTransGen (FrontierCover.Incident (piece H curve left right a b)) i j :=
  FrontierCover.isPreconnected_iff_reachable _ (cover H curve hcomplete left right hlcover hrcover)
    (accessible H hab curve hc hroot left right hlsub hrsub hlaccess hraccess)

end Decomposition
end LeanCanny.Connectivity.SlabCover
