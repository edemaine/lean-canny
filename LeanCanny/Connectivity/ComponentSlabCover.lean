/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.ClopenPathCover
public import LeanCanny.Connectivity.AccessibleArc
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.Finite.Prod

/-! # A closed path cover of the original closed slab

Attach each saturated interior component to a chosen clopen component in each
endpoint fiber. Connected endpoint limits make the union closed. The extended
critical branch joins its three parts. Using all valid triples of labels
avoids any choice of component representatives and preserves empty slices.
The overlap graph therefore preserves both paths and whole-slab connectivity.
-/

@[expose] public section

namespace LeanCanny.Connectivity.ComponentSlabCover
open Set
open scoped Classical

variable {X J L R : Type*} [TopologicalSpace X]

/-- Geometric data constructed by `PolynomialSlabCover` for a regular interval.
Endpoint regularity is not required. -/
structure InteriorData (p : X → ℝ) (a b : ℝ) (J : Type*) where
  piece : J → Set (p ⁻¹' Ioo a b)
  closed : ∀ j, IsClosed (piece j)
  cover : ∀ x, ∃ j, x ∈ piece j
  paths : ∀ j, ∀ x ∈ piece j, ∀ y ∈ piece j, JoinedIn (piece j) x y
  arc : J → ℝ → X
  continuous_arc : ∀ j, ContinuousOn (arc j) (Icc a b)
  arc_mem : ∀ j (t : Ioo a b), arc j t.val ∈ Subtype.val '' piece j
  level_left : ∀ j, p (arc j a) = a
  level_right : ∀ j, p (arc j b) = b
  limit_left : ∀ j, IsPreconnected (closure (Subtype.val '' piece j) ∩ p ⁻¹' {a})
  limit_right : ∀ j, IsPreconnected (closure (Subtype.val '' piece j) ∩ p ⁻¹' {b})

namespace InteriorData
variable {p : X → ℝ} {a b : ℝ} (D : InteriorData p a b J)

def ambient (j : J) : Set X := Subtype.val '' D.piece j

theorem ambient_subset (j : J) : D.ambient j ⊆ p ⁻¹' Ioo a b := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

theorem ambient_paths (j : J) (x : X) (hx : x ∈ D.ambient j)
    (y : X) (hy : y ∈ D.ambient j) : JoinedIn (D.ambient j) x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (D.paths j u hu v hv).map continuous_subtype_val.continuousOn

theorem closure_inside (j : J) : closure (D.ambient j) ∩ p ⁻¹' Ioo a b ⊆ D.ambient j := by
  rintro x ⟨hx, hpx⟩
  let z : p ⁻¹' Ioo a b := ⟨x, hpx⟩
  have he := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image (D.piece j)
  have hz : z ∈ closure (D.piece j) := by rw [he]; exact hx
  exact ⟨z, (D.closed j).closure_eq ▸ hz, rfl⟩

theorem endpoint_mem_closure (hab : a < b) (j : J) {c : ℝ} (hc : c ∈ Icc a b) :
    D.arc j c ∈ closure (D.ambient j) := by
  have hc' : c ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
  have hm := ((D.continuous_arc j c hc).mono Ioo_subset_Icc_self).mem_closure_image hc'
  exact closure_mono (by rintro z ⟨t, ht, rfl⟩; exact D.arc_mem j ⟨t, ht⟩) hm

end InteriorData

abbrev Index (J L R : Type*) := (J × L × R) ⊕ (L ⊕ R)

variable {p : X → ℝ} {a b : ℝ} (D : InteriorData p a b J)
  (left : ClopenPathCover (p ⁻¹' {a}) L) (right : ClopenPathCover (p ⁻¹' {b}) R)

def Valid (j : J) (l : L) (r : R) : Prop :=
  D.arc j a ∈ left.imagePiece l ∧ D.arc j b ∈ right.imagePiece r

noncomputable def ambientPiece : Index J L R → Set X :=
  Sum.elim (fun ⟨j, l, r⟩ => if Valid D left right j l r then
    closure (D.ambient j) ∪ left.imagePiece l ∪ right.imagePiece r else ∅)
    (Sum.elim left.imagePiece right.imagePiece)

noncomputable def piece : Index J L R → Set (p ⁻¹' Icc a b) :=
  fun i => Subtype.val ⁻¹' ambientPiece D left right i

theorem ambientPiece_closed (hp : Continuous p) (i : Index J L R) :
    IsClosed (ambientPiece D left right i) := by
  classical
  rcases i with ⟨j, l, r⟩ | (l | r)
  · by_cases h : Valid D left right j l r
    · simpa only [ambientPiece, Sum.elim_inl, h, ite_eq_left] using
        (isClosed_closure.union (left.imagePiece_closed (isClosed_singleton.preimage hp) l)).union
          (right.imagePiece_closed (isClosed_singleton.preimage hp) r)
    · simpa only [ambientPiece, Sum.elim_inl, ite_eq_right h] using (isClosed_empty : IsClosed (∅ : Set X))
  · exact left.imagePiece_closed (isClosed_singleton.preimage hp) l
  · exact right.imagePiece_closed (isClosed_singleton.preimage hp) r

theorem ambientPiece_subset (hp : Continuous p) (hab : a < b) (i : Index J L R) :
    ambientPiece D left right i ⊆ p ⁻¹' Icc a b := by
  classical
  rcases i with ⟨j, l, r⟩ | (l | r)
  · by_cases h : Valid D left right j l r
    · simp only [ambientPiece, Sum.elim_inl, h, ite_eq_left, union_subset_iff]
      exact ⟨⟨closure_minimal (fun x hx => Ioo_subset_Icc_self (D.ambient_subset j hx))
        (isClosed_Icc.preimage hp), fun x hx => by
          have he : p x = a := left.imagePiece_subset l hx
          change p x ∈ Icc a b
          rw [he]
          exact ⟨le_rfl, hab.le⟩⟩, fun x hx => by
        have he : p x = b := right.imagePiece_subset r hx
        change p x ∈ Icc a b
        rw [he]
        exact ⟨hab.le, le_rfl⟩⟩
    · simp only [ambientPiece, Sum.elim_inl, ite_eq_right h, empty_subset]
  · intro x hx
    have he : p x = a := left.imagePiece_subset l hx
    change p x ∈ Icc a b
    rw [he]
    exact ⟨le_rfl, hab.le⟩
  · intro x hx
    have he : p x = b := right.imagePiece_subset r hx
    change p x ∈ Icc a b
    rw [he]
    exact ⟨hab.le, le_rfl⟩

/-- No closure query is needed: a valid triple is just the interior component
and its two chosen endpoint pieces. Connected limits justify this equality. -/
theorem ambientPiece_middle_eq (hp : Continuous p) (hab : a < b)
    (j : J) (l : L) (r : R) (hvalid : Valid D left right j l r) :
    ambientPiece D left right (.inl (j, l, r)) =
      D.ambient j ∪ left.imagePiece l ∪ right.imagePiece r := by
  classical
  simp only [ambientPiece, Sum.elim_inl, hvalid, ite_eq_left]
  apply Subset.antisymm ?_ (union_subset_union (union_subset_union_left _ subset_closure) Subset.rfl)
  rintro x ((hx | hx) | hx)
  · have hxlevel : p x ∈ Icc a b := closure_minimal (t := p ⁻¹' Icc a b)
      (fun z hz => Ioo_subset_Icc_self (D.ambient_subset j hz)) (isClosed_Icc.preimage hp) hx
    by_cases ha : p x = a
    · have hkeep := left.subset_imagePiece_of_isPreconnected (D.limit_left j) inter_subset_right
        ⟨D.endpoint_mem_closure hab j ⟨le_rfl, hab.le⟩, D.level_left j⟩ hvalid.1
      exact Or.inl (Or.inr (hkeep ⟨hx, ha⟩))
    · by_cases hb : p x = b
      · have hkeep := right.subset_imagePiece_of_isPreconnected (D.limit_right j) inter_subset_right
          ⟨D.endpoint_mem_closure hab j ⟨hab.le, le_rfl⟩, D.level_right j⟩ hvalid.2
        exact Or.inr (hkeep ⟨hx, hb⟩)
      · exact Or.inl (Or.inl (D.closure_inside j ⟨hx,
          lt_of_le_of_ne hxlevel.1 (Ne.symm ha), lt_of_le_of_ne hxlevel.2 hb⟩))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

/-- The set expression used by recursive membership and overlap queries. -/
noncomputable def explicitPiece : Index J L R → Set X :=
  Sum.elim (fun ⟨j, l, r⟩ => if Valid D left right j l r then
    D.ambient j ∪ left.imagePiece l ∪ right.imagePiece r else ∅)
    (Sum.elim left.imagePiece right.imagePiece)

theorem ambientPiece_eq_explicit (hp : Continuous p) (hab : a < b) (i : Index J L R) :
    ambientPiece D left right i = explicitPiece D left right i := by
  classical
  rcases i with ⟨j, l, r⟩ | (l | r)
  · by_cases h : Valid D left right j l r
    · rw [ambientPiece_middle_eq D left right hp hab j l r h]
      simp only [explicitPiece, Sum.elim_inl, ite_eq_left h]
    · simp only [ambientPiece, explicitPiece, Sum.elim_inl, ite_eq_right h]
  · rfl
  · rfl

/-- The original closed slab's overlap queries contain no closure operator. -/
theorem overlap_iff_explicit (hp : Continuous p) (hab : a < b) (i j : Index J L R) :
    ClosedPathCover.Overlap (piece D left right) i j ↔
      (explicitPiece D left right i ∩ explicitPiece D left right j).Nonempty := by
  rw [← ambientPiece_eq_explicit D left right hp hab i, ← ambientPiece_eq_explicit D left right hp hab j]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x.val, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨⟨x, ambientPiece_subset D left right hp hab i hx⟩, hx, hy⟩

theorem cover (_hab : a < b) : ∀ x : p ⁻¹' Icc a b, ∃ i, x ∈ piece D left right i := by
  classical
  intro x
  rcases eq_or_lt_of_le x.property.1 with ha | ha
  · obtain ⟨l, hl⟩ := left.imagePiece_cover x.val ha.symm
    exact ⟨.inr (.inl l), hl⟩
  · rcases eq_or_lt_of_le x.property.2 with hb | hb
    · obtain ⟨r, hr⟩ := right.imagePiece_cover x.val hb
      exact ⟨.inr (.inr r), hr⟩
    · obtain ⟨j, hj⟩ := D.cover ⟨x.val, ha, hb⟩
      obtain ⟨l, hl⟩ := left.imagePiece_cover (D.arc j a) (D.level_left j)
      obtain ⟨r, hr⟩ := right.imagePiece_cover (D.arc j b) (D.level_right j)
      refine ⟨.inl (j, l, r), ?_⟩
      change x.val ∈ if Valid D left right j l r then
        closure (D.ambient j) ∪ left.imagePiece l ∪ right.imagePiece r else (∅ : Set X)
      rw [ite_eq_left ⟨hl, hr⟩]
      exact Or.inl (Or.inl (subset_closure ⟨⟨x.val, ha, hb⟩, hj, rfl⟩))

/-- Record validity uses only membership of branch endpoints in recursive
components and nonemptiness of the two endpoint records. -/
def ValidRecord : Index J L R → Prop :=
  Sum.elim (fun ⟨j, l, r⟩ => Valid D left right j l r)
    (Sum.elim (fun l => (left.piece l).Nonempty) (fun r => (right.piece r).Nonempty))

theorem nonempty_iff_validRecord (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b) (i : Index J L R) :
    (piece D left right i).Nonempty ↔ ValidRecord D left right i := by
  classical
  rcases i with ⟨j, l, r⟩ | (l | r)
  · constructor
    · rintro ⟨x, hx⟩
      by_contra h
      change ¬Valid D left right j l r at h
      change x.val ∈ if Valid D left right j l r then _ else (∅ : Set X) at hx
      rw [ite_eq_right h] at hx
      exact hx
    · intro h
      change Valid D left right j l r at h
      have hx : D.arc j t₀.val ∈ ambientPiece D left right (.inl (j, l, r)) := by
        change D.arc j t₀.val ∈ if Valid D left right j l r then _ else (∅ : Set X)
        rw [ite_eq_left h]
        exact Or.inl (Or.inl (subset_closure (D.arc_mem j t₀)))
      exact ⟨⟨D.arc j t₀.val, ambientPiece_subset D left right hp hab _ hx⟩, hx⟩
  · constructor
    · rintro ⟨x, y, hy, _⟩
      exact ⟨y, hy⟩
    · rintro ⟨x, hx⟩
      have hm : x.val ∈ ambientPiece D left right (.inr (.inl l)) := ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, ambientPiece_subset D left right hp hab _ hm⟩, hm⟩
  · constructor
    · rintro ⟨x, y, hy, _⟩
      exact ⟨y, hy⟩
    · rintro ⟨x, hx⟩
      have hm : x.val ∈ ambientPiece D left right (.inr (.inr r)) := ⟨x, hx, rfl⟩
      exact ⟨⟨x.val, ambientPiece_subset D left right hp hab _ hm⟩, hm⟩

theorem ambientPiece_paths (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b)
    (i : Index J L R) (x : X) (hx : x ∈ ambientPiece D left right i)
    (y : X) (hy : y ∈ ambientPiece D left right i) :
    JoinedIn (ambientPiece D left right i) x y := by
  classical
  rcases i with ⟨j, l, r⟩ | (l | r)
  · by_cases h : Valid D left right j l r
    · rw [ambientPiece_middle_eq D left right hp hab j l r h] at hx hy ⊢
      let U := D.ambient j ∪ left.imagePiece l ∪ right.imagePiece r
      have hcurve : D.arc j '' Icc a b ⊆ U := by
        rintro z ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.1 with ht₁ | ht₁
        · exact Or.inl (Or.inr (ht₁ ▸ h.1))
        · rcases eq_or_lt_of_le ht.2 with ht₂ | ht₂
          · exact Or.inr (ht₂.symm ▸ h.2)
          · exact Or.inl (Or.inl (D.arc_mem j ⟨t, ht₁, ht₂⟩))
      have hbranch (t : ℝ) (ht : t ∈ Icc a b) : JoinedIn U (D.arc j t) (D.arc j t₀.val) :=
        ((Convex.isPathConnected (convex_Icc a b) ⟨a, le_rfl, hab.le⟩).joinedIn t ht
          t₀.val (Ioo_subset_Icc_self t₀.property)).map (D.continuous_arc j) |>.mono hcurve
      have hto (z : X) (hz : z ∈ U) : JoinedIn U z (D.arc j t₀.val) := by
        rcases hz with (hz | hz) | hz
        · exact (D.ambient_paths j z hz _ (D.arc_mem j t₀)).mono
            (fun _ h => Or.inl (Or.inl h))
        · exact ((left.imagePiece_paths l z hz _ h.1).mono
            (fun _ h => Or.inl (Or.inr h))).trans (hbranch a ⟨le_rfl, hab.le⟩)
        · exact ((right.imagePiece_paths r z hz _ h.2).mono (fun _ h => Or.inr h)).trans
            (hbranch b ⟨hab.le, le_rfl⟩)
      exact (hto x hx).trans (hto y hy).symm
    · simp only [ambientPiece, Sum.elim_inl, ite_eq_right h, mem_empty_iff_false] at hx
  · exact left.imagePiece_paths l x hx y hy
  · exact right.imagePiece_paths r x hx y hy

theorem paths (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b)
    (i : Index J L R) (x : p ⁻¹' Icc a b) (hx : x ∈ piece D left right i)
    (y : p ⁻¹' Icc a b) (hy : y ∈ piece D left right i) : JoinedIn (piece D left right i) x y := by
  have hsub : ambientPiece D left right i ⊆ range (Subtype.val : p ⁻¹' Icc a b → X) := by
    intro z hz
    exact ⟨⟨z, ambientPiece_subset D left right hp hab i hz⟩, rfl⟩
  have he := Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image hx hy
  rw [piece, image_preimage_eq_of_subset hsub] at he
  exact he.mp (ambientPiece_paths D left right hp hab t₀ i x.val hx y.val hy)

/-- Only one endpoint component on each side is needed per interior label.
The final cover keeps a sum of label families, avoiding a product at each
recursive dimension. Selectors may be computed when queries need them. -/
abbrev SelectedIndex (J L R : Type*) := J ⊕ (L ⊕ R)

def selectedIndex (leftOf : J → L) (rightOf : J → R) : SelectedIndex J L R → Index J L R :=
  Sum.elim (fun j => .inl (j, leftOf j, rightOf j)) Sum.inr

noncomputable def selectedPiece (leftOf : J → L) (rightOf : J → R) :
    SelectedIndex J L R → Set (p ⁻¹' Icc a b) :=
  fun i => piece D left right (selectedIndex leftOf rightOf i)

theorem exists_selection : ∃ leftOf : J → L, ∃ rightOf : J → R,
    ∀ j, Valid D left right j (leftOf j) (rightOf j) := by
  classical
  choose leftOf hl using fun j => left.imagePiece_cover (D.arc j a) (D.level_left j)
  choose rightOf hr using fun j => right.imagePiece_cover (D.arc j b) (D.level_right j)
  exact ⟨leftOf, rightOf, fun j => ⟨hl j, hr j⟩⟩

variable (leftOf : J → L) (rightOf : J → R)
  (hselect : ∀ j, Valid D left right j (leftOf j) (rightOf j))

include hselect in
theorem selected_cover : ∀ x : p ⁻¹' Icc a b, ∃ i, x ∈ selectedPiece D left right leftOf rightOf i := by
  intro x
  rcases eq_or_lt_of_le x.property.1 with ha | ha
  · obtain ⟨l, hl⟩ := left.imagePiece_cover x.val ha.symm
    exact ⟨.inr (.inl l), hl⟩
  · rcases eq_or_lt_of_le x.property.2 with hb | hb
    · obtain ⟨r, hr⟩ := right.imagePiece_cover x.val hb
      exact ⟨.inr (.inr r), hr⟩
    · obtain ⟨j, hj⟩ := D.cover ⟨x.val, ha, hb⟩
      refine ⟨.inl j, ?_⟩
      change x.val ∈ if Valid D left right j (leftOf j) (rightOf j) then
        closure (D.ambient j) ∪ left.imagePiece (leftOf j) ∪ right.imagePiece (rightOf j) else (∅ : Set X)
      rw [ite_eq_left (hselect j)]
      exact Or.inl (Or.inl (subset_closure ⟨⟨x.val, ha, hb⟩, hj, rfl⟩))

theorem selected_closed (hp : Continuous p) (i : SelectedIndex J L R) :
    IsClosed (selectedPiece D left right leftOf rightOf i) :=
  (ambientPiece_closed D left right hp _).preimage continuous_subtype_val

theorem selected_paths (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b)
    (i : SelectedIndex J L R) (x : p ⁻¹' Icc a b) (hx : x ∈ selectedPiece D left right leftOf rightOf i)
    (y : p ⁻¹' Icc a b) (hy : y ∈ selectedPiece D left right leftOf rightOf i) :
    JoinedIn (selectedPiece D left right leftOf rightOf i) x y :=
  paths D left right hp hab t₀ _ x hx y hy

theorem selected_overlap_iff_explicit (hp : Continuous p) (hab : a < b) (i j : SelectedIndex J L R) :
    ClosedPathCover.Overlap (selectedPiece D left right leftOf rightOf) i j ↔
      (explicitPiece D left right (selectedIndex leftOf rightOf i) ∩
        explicitPiece D left right (selectedIndex leftOf rightOf j)).Nonempty :=
  overlap_iff_explicit D left right hp hab _ _

variable [Finite J] [Finite L] [Finite R]

theorem selectedIndex_card : Nat.card (SelectedIndex J L R) = Nat.card J + (Nat.card L + Nat.card R) := by
  simp only [SelectedIndex, Nat.card_sum]

include hselect in
theorem selected_joinedIn_iff_reachable (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b)
    {i j : SelectedIndex J L R} {x y : p ⁻¹' Icc a b}
    (hx : x ∈ selectedPiece D left right leftOf rightOf i)
    (hy : y ∈ selectedPiece D left right leftOf rightOf j) :
    JoinedIn univ x y ↔
      Relation.ReflTransGen (ClosedPathCover.Overlap (selectedPiece D left right leftOf rightOf)) i j :=
  ClosedPathCover.joinedIn_iff_reachable _ (selected_closed D left right leftOf rightOf hp)
    (selected_cover D left right leftOf rightOf hselect)
    (selected_paths D left right leftOf rightOf hp hab t₀) hx hy

include hselect in
theorem selected_isPreconnected_iff_reachable (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b) :
    IsPreconnected (univ : Set (p ⁻¹' Icc a b)) ↔
      ∀ i j, (selectedPiece D left right leftOf rightOf i).Nonempty →
        (selectedPiece D left right leftOf rightOf j).Nonempty →
        Relation.ReflTransGen (ClosedPathCover.Overlap (selectedPiece D left right leftOf rightOf)) i j :=
  ClosedPathCover.isPreconnected_iff_reachable _ (selected_closed D left right leftOf rightOf hp)
    (selected_cover D left right leftOf rightOf hselect)
    (selected_paths D left right leftOf rightOf hp hab t₀)

theorem joinedIn_iff_reachable (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b)
    {i j : Index J L R} {x y : p ⁻¹' Icc a b}
    (hx : x ∈ piece D left right i) (hy : y ∈ piece D left right j) :
    JoinedIn univ x y ↔ Relation.ReflTransGen (ClosedPathCover.Overlap (piece D left right)) i j :=
  ClosedPathCover.joinedIn_iff_reachable _
    (fun i => (ambientPiece_closed D left right hp i).preimage continuous_subtype_val)
    (cover D left right hab) (paths D left right hp hab t₀) hx hy

theorem isPreconnected_iff_reachable (hp : Continuous p) (hab : a < b) (t₀ : Ioo a b) :
    IsPreconnected (univ : Set (p ⁻¹' Icc a b)) ↔
      ∀ i j, (piece D left right i).Nonempty → (piece D left right j).Nonempty →
        Relation.ReflTransGen (ClosedPathCover.Overlap (piece D left right)) i j :=
  ClosedPathCover.isPreconnected_iff_reachable _
    (fun i => (ambientPiece_closed D left right hp i).preimage continuous_subtype_val)
    (cover D left right hab) (paths D left right hp hab t₀)

end LeanCanny.Connectivity.ComponentSlabCover
