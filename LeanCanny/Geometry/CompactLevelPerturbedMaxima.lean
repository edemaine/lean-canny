/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactLevelMaxima

/-! # Stability of small-level maxima under objective perturbation

Recovery and compact separation put small-level maxima near a unique
zero-level maximum. The conclusion persists for continuous objectives
uniformly close to the original one on the compact neighborhood.
-/

@[expose] public section

namespace LeanCanny.Geometry.CompactLevelMaxima
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_local_max_near_for_close_objectives (K : Set X) (hK : IsCompact K) (g φ : X → ℝ)
    (hg : Continuous g) (hφ : Continuous φ) (p : X) (hpK : p ∈ interior K)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x)
    (hunique : ∀ x ∈ K, g x = 0 → φ p ≤ φ x → x = p)
    (hrec : LocalLevelApproximation.Recovery g p) (U : Set X) (hU : U ∈ nhds p) :
    ∃ a : ℝ, 0 < a ∧ ∃ e : ℝ, 0 < e ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ ψ : X → ℝ, Continuous ψ → (∀ x ∈ K, |ψ x - φ x| < e) →
        ∃ x ∈ U, g x = alpha ∧ IsLocalMaxOn ψ {y | g y = alpha} x := by
  let V := interior U ∩ interior K
  have hV : IsOpen V := isOpen_interior.inter isOpen_interior
  have hpV : p ∈ V := ⟨mem_interior_iff_mem_nhds.mpr hU, hpK⟩
  obtain ⟨a, ha, hm⟩ := CompactLevelConvergence.approximate_maximum_in_open
    K hK g φ hg hφ p hnonneg hunique V hV hpV
  have he : 0 < a / 3 := by linarith
  obtain ⟨b, hb, hr⟩ := LocalLevelApproximation.high_value g φ p hrec hφ K hpK (a / 3) he
  refine ⟨min a b, lt_min ha hb, a / 3, he, ?_⟩
  intro alpha hp hs ψ hψ hclose
  obtain ⟨y, hyK, hy, hφy⟩ := hr alpha hp (lt_of_lt_of_le hs (min_le_right _ _))
  have hlevel : IsCompact (K ∩ {x | g x = alpha}) := hK.inter_right (isClosed_eq hg continuous_const)
  obtain ⟨x, hx, hmax⟩ := hlevel.exists_isMaxOn ⟨y, hyK, hy⟩ hψ.continuousOn
  have hxe : g x ≤ a := by rw [hx.2]; exact (lt_of_lt_of_le hs (min_le_left _ _)).le
  have hxy : ψ y ≤ ψ x := hmax ⟨hyK, hy⟩
  have hxclose := abs_lt.mp (hclose x hx.1)
  have hyclose := abs_lt.mp (hclose y hyK)
  have hobj : φ p - a ≤ φ x := by linarith [hxclose.2, hyclose.1]
  have hxV := hm x hx.1 hxe hobj
  refine ⟨x, interior_subset hxV.1, hx.2, ?_⟩
  have hKn : K ∈ nhds x := mem_interior_iff_mem_nhds.mp hxV.2
  have hKe : ∀ᶠ z in nhds x, z ∈ K := hKn
  filter_upwards [hKe.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzK hzlevel
  exact hmax ⟨hzK, hzlevel⟩

end LeanCanny.Geometry.CompactLevelMaxima
