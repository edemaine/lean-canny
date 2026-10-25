/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ConnectedSlabLimit
public import Mathlib.Topology.Connected.Clopen

/-! # Exact component limits of compact sublevel neighborhoods

Components commute with decreasing compact intersections at a retained point.
Consequently, two zeros lie in the same component precisely when they remain
in the same component of every positive sublevel neighborhood. The zero fiber
may be singular. This limit statement supplies neither a finite effective
tolerance nor a conversion from connected components to paths.
-/

@[expose] public section
namespace LeanCanny.Geometry.CompactSublevelComponents
open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem isCompact_component (K : Set X) (hK : IsCompact K) (x : X) (hx : x ∈ K) :
    IsCompact (connectedComponentIn K x) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

theorem component_iInter {ι : Type*} [Nonempty ι] (K : ι → Set X)
    (hdir : Directed (· ⊇ ·) K) (hcompact : ∀ i, IsCompact (K i))
    (x : X) (hx : x ∈ ⋂ i, K i) :
    connectedComponentIn (⋂ i, K i) x = ⋂ i, connectedComponentIn (K i) x := by
  apply Subset.antisymm
  · intro y hy
    exact mem_iInter.mpr (fun i => connectedComponentIn_mono x (iInter_subset K i) hy)
  · have hdir' : Directed (· ⊇ ·) (fun i => connectedComponentIn (K i) x) := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := hdir i j
      exact ⟨k, connectedComponentIn_mono x hki, connectedComponentIn_mono x hkj⟩
    have hconn := ConnectedSlabLimit.isPreconnected_iInter (fun i => connectedComponentIn (K i) x)
      hdir' (fun i => isCompact_component (K i) (hcompact i) x (mem_iInter.mp hx i))
      (fun _ => isPreconnected_connectedComponentIn)
    apply hconn.subset_connectedComponentIn
    · exact mem_iInter.mpr (fun i => mem_connectedComponentIn (mem_iInter.mp hx i))
    · exact subset_iInter (fun i => (iInter_subset _ i).trans (connectedComponentIn_subset (K i) x))

def sublevel (K : Set X) (g : X → ℝ) (e : ℝ) : Set X := K ∩ {x | g x ≤ e}

theorem sublevel_component (K : Set X) (hK : IsCompact K) (g : X → ℝ) (hg : Continuous g)
    (x : X) (hx : x ∈ sublevel K g 0) :
    connectedComponentIn (sublevel K g 0) x =
      ⋂ e : Ioi (0 : ℝ), connectedComponentIn (sublevel K g e.val) x := by
  let : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  have he : (⋂ e : Ioi (0 : ℝ), sublevel K g e.val) = sublevel K g 0 := by
    ext y
    simp only [mem_iInter, sublevel, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨(h ⟨1, by norm_num⟩).1, ?_⟩
      by_contra hn
      have hp : 0 < g y := lt_of_not_ge hn
      have hm := (h ⟨g y / 2, half_pos hp⟩).2
      linarith
    · rintro ⟨hy, hgy⟩ e
      exact ⟨hy, hgy.trans e.property.le⟩
  have hc (e : Ioi (0 : ℝ)) : IsCompact (sublevel K g e.val) :=
    hK.inter_right (isClosed_le hg continuous_const)
  have hd : Directed (· ⊇ ·) (fun e : Ioi (0 : ℝ) => sublevel K g e.val) := by
    intro e f
    refine ⟨⟨min e.val f.val, lt_min e.property f.property⟩, ?_, ?_⟩
    · intro y hy
      change y ∈ K ∧ g y ≤ min e.val f.val at hy
      exact ⟨hy.1, hy.2.trans (min_le_left _ _)⟩
    · intro y hy
      change y ∈ K ∧ g y ≤ min e.val f.val at hy
      exact ⟨hy.1, hy.2.trans (min_le_right _ _)⟩
  simpa only [he] using component_iInter (fun e : Ioi (0 : ℝ) => sublevel K g e.val) hd hc x (he.symm ▸ hx)

theorem zero_component (K : Set X) (hK : IsCompact K) (g : X → ℝ) (hg : Continuous g)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x) (x : X) (hx : x ∈ K) (hx0 : g x = 0) :
    connectedComponentIn (K ∩ g ⁻¹' {0}) x =
      ⋂ e : Ioi (0 : ℝ), connectedComponentIn (sublevel K g e.val) x := by
  have he : K ∩ g ⁻¹' {0} = sublevel K g 0 := by
    ext y
    change (y ∈ K ∧ g y = 0) ↔ y ∈ K ∧ g y ≤ 0
    exact ⟨fun h => ⟨h.1, h.2.le⟩, fun h => ⟨h.1, le_antisymm h.2 (hnonneg y h.1)⟩⟩
  rw [he]
  exact sublevel_component K hK g hg x ⟨hx, hx0.le⟩

theorem mem_zero_component_iff (K : Set X) (hK : IsCompact K) (g : X → ℝ) (hg : Continuous g)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x) (x y : X) (hx : x ∈ K) (hx0 : g x = 0) :
    y ∈ connectedComponentIn (K ∩ g ⁻¹' {0}) x ↔
      ∀ e : ℝ, 0 < e → y ∈ connectedComponentIn (sublevel K g e) x := by
  rw [zero_component K hK g hg hnonneg x hx hx0]
  exact ⟨fun h e he => mem_iInter.mp h ⟨e, he⟩, fun h => mem_iInter.mpr (fun e => h e.val e.property)⟩

theorem separated_at_positive_sublevel (K : Set X) (hK : IsCompact K) (g : X → ℝ) (hg : Continuous g)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x) (x y : X) (hx : x ∈ K) (hx0 : g x = 0)
    (hxy : y ∉ connectedComponentIn (K ∩ g ⁻¹' {0}) x) :
    ∃ e : ℝ, 0 < e ∧ y ∉ connectedComponentIn (sublevel K g e) x := by
  classical
  by_contra h
  push Not at h
  exact hxy ((mem_zero_component_iff K hK g hg hnonneg x y hx hx0).mpr h)

end LeanCanny.Geometry.CompactSublevelComponents
