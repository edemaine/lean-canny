/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.SlabCover

/-! # Finite-fiber slabs with explicit endpoint incidence

Complete disjoint arcs and finite endpoint fibers construct a finite graph
without supplied endpoint covers. Vertices are interior arcs and actual
endpoint roots. Edges are equality of vertices or equality with an arc's
endpoint. The graph preserves paths and whole-slab connectedness, including
isolated endpoint roots and empty slabs. Effective endpoint equality and
bounded encodings remain separate obligations.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FiniteFiberSlab
open Set
variable {E J : Type*} [TopologicalSpace E] [T2Space E]

abbrev Fiber (H : ℝ → E → Prop) (t : ℝ) := {x : E // H t x}
abbrev Index (H : ℝ → E → Prop) (J : Type*) (a b : ℝ) :=
  SlabCover.Index J (Fiber H a) (Fiber H b)

def singletonPiece (H : ℝ → E → Prop) (t : ℝ) (i : Fiber H t) : Set E := {i.val}

def piece (H : ℝ → E → Prop) (curve : J → ℝ → E) (a b : ℝ) :
    Index H J a b → Set (SlabCover.Space H a b) :=
  SlabCover.piece H curve (singletonPiece H a) (singletonPiece H b) a b

/-- No closure query occurs in this endpoint graph. -/
def Edge (H : ℝ → E → Prop) (curve : J → ℝ → E) (a b : ℝ) : Index H J a b → Index H J a b → Prop
  | .inl i, .inl j => i = j
  | .inl i, .inr (.inl l) => curve i a = l.val
  | .inr (.inl l), .inl i => curve i a = l.val
  | .inl i, .inr (.inr r) => curve i b = r.val
  | .inr (.inr r), .inl i => curve i b = r.val
  | .inr (.inl l), .inr (.inl k) => l = k
  | .inr (.inr r), .inr (.inr k) => r = k
  | .inr (.inl _), .inr (.inr _) => False
  | .inr (.inr _), .inr (.inl _) => False

omit [TopologicalSpace E] [T2Space E] in
lemma singleton_subset (H : ℝ → E → Prop) (t : ℝ) (i : Fiber H t) (x : E)
    (hx : x ∈ singletonPiece H t i) : H t x := by
  rw [show x = i.val from hx]
  exact i.property

omit [TopologicalSpace E] [T2Space E] in
lemma singleton_cover (H : ℝ → E → Prop) (t : ℝ) (x : E) (hx : H t x) :
    ∃ i, x ∈ singletonPiece H t i := ⟨⟨x, hx⟩, rfl⟩

lemma singleton_accessible (H : ℝ → E → Prop) (t : ℝ) (i : Fiber H t) :
    FrontierCover.Accessible (singletonPiece H t i) := FrontierCover.accessible_singleton i.val

lemma singleton_incident_iff (H : ℝ → E → Prop) (t : ℝ) (i j : Fiber H t) :
    FrontierCover.Incident (singletonPiece H t) i j ↔ i = j := by
  simp only [FrontierCover.Incident, singletonPiece, closure_singleton]
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hy, hx⟩)
    · exact Subtype.ext (hx.symm.trans hy)
    · exact Subtype.ext (hx.symm.trans hy)
  · rintro rfl
    exact Or.inl ⟨i.val, rfl, rfl⟩

section Arcs
variable (H : ℝ → E → Prop) {a b : ℝ} (hab : a < b) (curve : J → ℝ → E)
  (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
  (hroot : ∀ j t, t ∈ Icc a b → H t (curve j t))
  (hcomplete : ∀ t ∈ Ioo a b, ∀ x, H t x → ∃ j, curve j t = x)
  (hinj : ∀ t ∈ Ioo a b, Function.Injective (fun j => curve j t))

include hcomplete in
omit [TopologicalSpace E] [T2Space E] in
lemma cover (z : SlabCover.Space H a b) : ∃ i, z ∈ piece H curve a b i :=
  SlabCover.cover H curve hcomplete _ _ (singleton_cover H a) (singleton_cover H b) z

include hab hc hroot in
lemma accessible (i : Index H J a b) : FrontierCover.Accessible (piece H curve a b i) :=
  SlabCover.accessible H hab curve hc hroot _ _ (singleton_subset H a) (singleton_subset H b)
    (singleton_accessible H a) (singleton_accessible H b) i

include hab hc hroot hinj in
lemma incident_iff (i j : Index H J a b) :
    FrontierCover.Incident (piece H curve a b) i j ↔ Edge H curve a b i j := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · exact SlabCover.incident_arcs_iff H hab curve hc hroot _ _
      (singleton_subset H a) (singleton_subset H b) hinj i j
  · exact SlabCover.incident_arc_left_iff H hab curve hc hroot _ _
      (singleton_subset H a) (singleton_subset H b) i j
  · exact SlabCover.incident_arc_right_iff H hab curve hc hroot _ _
      (singleton_subset H a) (singleton_subset H b) i j
  · rw [FrontierCover.incident_symm]
    exact SlabCover.incident_arc_left_iff H hab curve hc hroot _ _
      (singleton_subset H a) (singleton_subset H b) j i
  · exact (SlabCover.incident_left_iff H hab curve hroot _ _
      (singleton_subset H a) (singleton_subset H b) i j).trans (singleton_incident_iff H a i j)
  · exact iff_false_intro (SlabCover.not_incident_left_right H hab curve hroot _ _
      (singleton_subset H a) (singleton_subset H b) i j)
  · rw [FrontierCover.incident_symm]
    exact SlabCover.incident_arc_right_iff H hab curve hc hroot _ _
      (singleton_subset H a) (singleton_subset H b) j i
  · rw [FrontierCover.incident_symm]
    exact iff_false_intro (SlabCover.not_incident_left_right H hab curve hroot _ _
      (singleton_subset H a) (singleton_subset H b) j i)
  · exact (SlabCover.incident_right_iff H hab curve hroot _ _
      (singleton_subset H a) (singleton_subset H b) i j).trans (singleton_incident_iff H b i j)

include hab hroot in
omit [TopologicalSpace E] [T2Space E] in
lemma nonempty_piece (i : Index H J a b) : (piece H curve a b i).Nonempty := by
  rcases i with j | (l | r)
  · let t := (a + b) / 2
    have ht : t ∈ Ioo a b := by dsimp [t]; constructor <;> linarith
    exact ⟨⟨(t, curve j t), Ioo_subset_Icc_self ht, hroot j t (Ioo_subset_Icc_self ht)⟩,
      t, ht, rfl⟩
  · exact ⟨⟨(a, l.val), ⟨le_rfl, hab.le⟩, l.property⟩, l.val, rfl, rfl⟩
  · exact ⟨⟨(b, r.val), ⟨hab.le, le_rfl⟩, r.property⟩, r.val, rfl, rfl⟩

variable [Finite J] [Finite (Fiber H a)] [Finite (Fiber H b)]

include hab hc hroot hcomplete hinj in
lemma joinedIn_iff_reachable {i j : Index H J a b} {x y : SlabCover.Space H a b}
    (hx : x ∈ piece H curve a b i) (hy : y ∈ piece H curve a b j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (Edge H curve a b) i j := by
  have he : FrontierCover.Incident (piece H curve a b) = Edge H curve a b :=
    funext (fun i => funext (fun j => propext (incident_iff H hab curve hc hroot hinj i j)))
  rw [← he]
  exact FrontierCover.joinedIn_iff_reachable _ (cover H curve hcomplete)
    (accessible H hab curve hc hroot) hx hy

include hab hc hroot hcomplete hinj in
lemma isPreconnected_iff_reachable :
    IsPreconnected (univ : Set (SlabCover.Space H a b)) ↔
      ∀ i j, Relation.ReflTransGen (Edge H curve a b) i j := by
  have he : FrontierCover.Incident (piece H curve a b) = Edge H curve a b :=
    funext (fun i => funext (fun j => propext (incident_iff H hab curve hc hroot hinj i j)))
  rw [← he]
  exact (FrontierCover.isPreconnected_iff_reachable _ (cover H curve hcomplete)
    (accessible H hab curve hc hroot)).trans
    ⟨fun h i j => h i j (nonempty_piece H hab curve hroot i) (nonempty_piece H hab curve hroot j),
      fun h i j _ _ => h i j⟩

end Arcs
end LeanCanny.Connectivity.FiniteFiberSlab
