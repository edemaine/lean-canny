/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AccessibleArc

/-! # Arc incidence at critical slices

An extended graph arc has exactly the expected closure. Its frontier incidence
with a piece contained in an endpoint slice is equivalent to membership of the
single endpoint in that piece. Thus this geometric adjacency condition does
not require a general closure-membership routine.
-/

@[expose] public section

namespace LeanCanny.Connectivity.FrontierCover
open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A continuous endpoint extension gives the entire closure of an open arc. -/
theorem closure_open_arc {a b : ℝ} (hab : a < b) {f : ℝ → X}
    (hf : ContinuousOn f (Icc a b)) :
    closure (f '' Ioo a b) = f '' Icc a b := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image_of_continuousOn hf).isClosed
  · rintro z ⟨t, ht, rfl⟩
    have htcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    exact ((hf t ht).mono Ioo_subset_Icc_self).mem_closure_image htcl

theorem mem_closure_graphArc_iff {a b : ℝ} (hab : a < b) {f : ℝ → X}
    (hf : ContinuousOn f (Icc a b)) {z : ℝ × X} :
    z ∈ closure ((fun t => (t, f t)) '' Ioo a b) ↔
      z.1 ∈ Icc a b ∧ z.2 = f z.1 := by
  have hgraph : ContinuousOn (fun t => (t, f t)) (Icc a b) :=
    continuous_id.continuousOn.prodMk hf
  rw [closure_open_arc hab hgraph]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, rfl⟩
  · rintro ⟨ht, hz⟩
    exact ⟨z.1, ht, Prod.ext rfl hz.symm⟩

/-- A graph arc meets a fixed slice in precisely its point at that parameter. -/
theorem slice_inter_closure_graphArc_iff {a b c : ℝ} (hab : a < b)
    {f : ℝ → X} (hf : ContinuousOn f (Icc a b)) (hc : c ∈ Icc a b)
    {s : Set (ℝ × X)} (hs : ∀ z ∈ s, z.1 = c) :
    (s ∩ closure ((fun t => (t, f t)) '' Ioo a b)).Nonempty ↔ (c, f c) ∈ s := by
  constructor
  · rintro ⟨z, hz, hcl⟩
    have hparam := hs z hz
    have hvalue := (mem_closure_graphArc_iff hab hf).mp hcl
    have heq : z = (c, f c) := Prod.ext hparam (hvalue.2.trans (congrArg f hparam))
    simpa only [heq] using hz
  · intro h
    exact ⟨(c, f c), h, (mem_closure_graphArc_iff hab hf).mpr ⟨hc, rfl⟩⟩

/-- At a boundary parameter, frontier incidence with a slice piece is just
endpoint membership. A limit of points in the slice cannot enter the arc's
open parameter interval. The slice piece itself need not be closed. -/
theorem incident_graphArc_slice_iff {a b c : ℝ} (hab : a < b)
    {f : ℝ → X} (hf : ContinuousOn f (Icc a b)) (hc : c ∈ Icc a b)
    (hcnot : c ∉ Ioo a b) {s : Set (ℝ × X)} (hs : ∀ z ∈ s, z.1 = c) :
    ((s ∩ closure ((fun t => (t, f t)) '' Ioo a b)).Nonempty ∨
      (((fun t => (t, f t)) '' Ioo a b) ∩ closure s).Nonempty) ↔
        (c, f c) ∈ s := by
  have hclosed : closure s ⊆ {z : ℝ × X | z.1 = c} :=
    closure_minimal hs (isClosed_eq continuous_fst continuous_const)
  rw [slice_inter_closure_graphArc_iff hab hf hc hs]
  constructor
  · rintro (h | ⟨z, ⟨t, ht, rfl⟩, hcl⟩)
    · exact h
    · have heq : t = c := hclosed hcl
      exact (hcnot (heq ▸ ht)).elim
  · exact Or.inl

/-- Disjoint graph branches have no frontier incidence in the open slab.
They may still meet at an endpoint, which is represented by a slice piece. -/
theorem incident_graphArcs_iff {J : Type*} {a b : ℝ} (hab : a < b)
    (f : J → ℝ → X) (hf : ∀ j, ContinuousOn (f j) (Icc a b))
    (hinj : ∀ t ∈ Ioo a b, Function.Injective (fun j => f j t)) (i j : J) :
    (( ((fun t => (t, f i t)) '' Ioo a b) ∩
        closure ((fun t => (t, f j t)) '' Ioo a b)).Nonempty ∨
      (((fun t => (t, f j t)) '' Ioo a b) ∩
        closure ((fun t => (t, f i t)) '' Ioo a b)).Nonempty) ↔ i = j := by
  have one_way (i j : J)
      (h : (((fun t => (t, f i t)) '' Ioo a b) ∩
        closure ((fun t => (t, f j t)) '' Ioo a b)).Nonempty) : i = j := by
    obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := h
    exact hinj t ht ((mem_closure_graphArc_iff hab (hf j)).mp hz).2
  constructor
  · rintro (h | h)
    · exact one_way i j h
    · exact (one_way j i h).symm
  · rintro rfl
    obtain ⟨t, ht⟩ := nonempty_Ioo.mpr hab
    exact Or.inl ⟨(t, f i t), ⟨t, ht, rfl⟩, subset_closure ⟨t, ht, rfl⟩⟩

omit [T2Space X] in
/-- Slice embeddings preserve the incidence relation, including closures of
nonclosed pieces inside the slice. -/
theorem incident_slice_image_iff {J : Type*} (s : J → Set X) (c : ℝ) (i j : J) :
    Incident (fun k => (fun x => (c, x)) '' s k) i j ↔ Incident s i j := by
  have hcl (k : J) : closure ((fun x => (c, x)) '' s k) =
      (fun x => (c, x)) '' closure (s k) :=
    (isClosedMap_prodMk_left c).closure_image_eq_of_continuous
      (continuous_const.prodMk continuous_id) _
  simp only [Incident, hcl]
  constructor
  · rintro (⟨z, ⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ | ⟨z, ⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩)
    · have hyx : y = x := congrArg Prod.snd hxy
      exact Or.inl ⟨x, hx, by simpa only [hyx] using hy⟩
    · have hyx : y = x := congrArg Prod.snd hxy
      exact Or.inr ⟨x, hx, by simpa only [hyx] using hy⟩
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact Or.inl ⟨(c, x), ⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
    · exact Or.inr ⟨(c, x), ⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩

omit [T2Space X] in
theorem not_incident_distinct_slices {c d : ℝ} (hcd : c ≠ d)
    {s t : Set (ℝ × X)} (hs : ∀ z ∈ s, z.1 = c) (ht : ∀ z ∈ t, z.1 = d) :
    ¬ ((s ∩ closure t).Nonempty ∨ (t ∩ closure s).Nonempty) := by
  have hcs : closure s ⊆ {z : ℝ × X | z.1 = c} :=
    closure_minimal hs (isClosed_eq continuous_fst continuous_const)
  have hct : closure t ⊆ {z : ℝ × X | z.1 = d} :=
    closure_minimal ht (isClosed_eq continuous_fst continuous_const)
  rintro (⟨z, hz, hcl⟩ | ⟨z, hz, hcl⟩)
  · exact hcd ((hs z hz).symm.trans (hct hcl))
  · exact hcd ((hcs hcl).symm.trans (ht z hz))

end LeanCanny.Connectivity.FrontierCover
