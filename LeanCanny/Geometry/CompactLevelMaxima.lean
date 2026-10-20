/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactLevelConvergence
public import LeanCanny.Geometry.LocalLevelApproximation

/-! # Local maxima on small levels near a unique zero-level maximum

Recovery of small levels near the original point supplies high objective values.
Compact separation forces the level maxima into any prescribed neighborhood,
including the interior of the compact set. They are consequently local maxima
on the full level set.
-/

@[expose] public section

namespace LeanCanny.Geometry.CompactLevelMaxima
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_local_max_near (K : Set X) (hK : IsCompact K) (g φ : X → ℝ)
    (hg : Continuous g) (hφ : Continuous φ) (p : X) (hpK : p ∈ interior K)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x)
    (hunique : ∀ x ∈ K, g x = 0 → φ p ≤ φ x → x = p)
    (hrec : LocalLevelApproximation.Recovery g p) (U : Set X) (hU : U ∈ nhds p) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ x ∈ U, g x = alpha ∧ IsLocalMaxOn φ {y | g y = alpha} x := by
  let V := interior U ∩ interior K
  have hV : IsOpen V := isOpen_interior.inter isOpen_interior
  have hpV : p ∈ V := ⟨mem_interior_iff_mem_nhds.mpr hU, hpK⟩
  obtain ⟨e, he, hm⟩ := CompactLevelConvergence.approximate_maximum_in_open
    K hK g φ hg hφ p hnonneg hunique V hV hpV
  obtain ⟨b, hb, hr⟩ := LocalLevelApproximation.high_value g φ p hrec hφ K hpK e he
  refine ⟨min e b, lt_min he hb, ?_⟩
  intro alpha hp hs
  obtain ⟨y, hyK, hy, hφy⟩ := hr alpha hp (lt_of_lt_of_le hs (min_le_right _ _))
  have hlevel : IsCompact (K ∩ {x | g x = alpha}) := hK.inter_right (isClosed_eq hg continuous_const)
  obtain ⟨x, hx, hmax⟩ := hlevel.exists_isMaxOn ⟨y, hyK, hy⟩ hφ.continuousOn
  have hxe : g x ≤ e := by rw [hx.2]; exact (lt_of_lt_of_le hs (min_le_left _ _)).le
  have hobj : φ p - e ≤ φ x := hφy.le.trans (hmax ⟨hyK, hy⟩)
  have hxV := hm x hx.1 hxe hobj
  refine ⟨x, interior_subset hxV.1, hx.2, ?_⟩
  have hKn : K ∈ nhds x := mem_interior_iff_mem_nhds.mp hxV.2
  have hKe : ∀ᶠ z in nhds x, z ∈ K := hKn
  filter_upwards [hKe.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzK hzlevel
  exact hmax ⟨hzK, hzlevel⟩

end LeanCanny.Geometry.CompactLevelMaxima
