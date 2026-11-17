/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoerciveMinimum

/-! # Continuity and monotonicity of coercive minimum values -/

public section

namespace LeanCanny.CountingHierarchy

open Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X]

@[expose] noncomputable def coerciveMinimumValue (F G : X → ℝ) (u : ℝ) : ℝ :=
  sInf (Set.range (fun x => G x + u * F x))

omit [MetricSpace X] in
theorem coerciveMinimumValue_eq_of_minimizer (F G : X → ℝ) (u : ℝ) (x : X)
    (hx : IsMinOn (fun y => G y + u * F y) univ x) :
    coerciveMinimumValue F G u = G x + u * F x := by
  apply IsLeast.csInf_eq
  refine ⟨Set.mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hx (mem_univ y)

theorem coerciveMinimumValue_le (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B})
    (x₀ : X) (u : ℝ) (hu : 0 ≤ u) (y : X) :
    coerciveMinimumValue F G u ≤ G y + u * F y := by
  obtain ⟨x, hx⟩ := exists_minimizer_of_compact_sublevels F G hF hG hFn hcompact x₀ u hu
  rw [coerciveMinimumValue_eq_of_minimizer F G u x hx]
  exact hx (mem_univ y)

theorem coerciveMinimumValue_monotoneOn (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) :
    MonotoneOn (coerciveMinimumValue F G) (Ici 0) := by
  intro u hu v hv huv
  obtain ⟨x, hx⟩ := exists_minimizer_of_compact_sublevels F G hF hG hFn hcompact x₀ v hv
  rw [coerciveMinimumValue_eq_of_minimizer F G v x hx]
  exact (coerciveMinimumValue_le F G hF hG hFn hcompact x₀ u hu x).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right huv (hFn x)))

theorem coerciveMinimumValue_continuousOn_Icc (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) (U : ℝ) :
    ContinuousOn (coerciveMinimumValue F G) (Icc 0 U) := by
  let B := G x₀ + U * F x₀
  let S := {x | G x ≤ B}
  have hjoint : Continuous (fun z : ℝ × X => G z.2 + z.1 * F z.2) :=
    (hG.comp continuous_snd).add (continuous_fst.mul (hF.comp continuous_snd))
  have hc : Continuous (fun u : ℝ => sInf ((fun x => G x + u * F x) '' S)) :=
    (hcompact B).continuous_sInf hjoint
  apply hc.continuousOn.congr
  intro u hu
  obtain ⟨x, hx⟩ := exists_minimizer_of_compact_sublevels F G hF hG hFn hcompact x₀ u hu.1
  have hm : G x + u * F x ≤ B :=
    (hx (mem_univ x₀)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hu.2 (hFn x₀)))
  have hxS : x ∈ S := (le_add_of_nonneg_right (mul_nonneg hu.1 (hFn x))).trans hm
  have hinf : sInf ((fun y => G y + u * F y) '' S) = G x + u * F x := by
    apply IsLeast.csInf_eq
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rintro _ ⟨y, _hy, rfl⟩
    exact hx (mem_univ y)
  exact (coerciveMinimumValue_eq_of_minimizer F G u x hx).trans hinf.symm

theorem coerciveMinimumValue_continuousOn (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) :
    ContinuousOn (coerciveMinimumValue F G) (Ici 0) := by
  intro u hu
  apply (coerciveMinimumValue_continuousOn_Icc F G hF hG hFn hcompact x₀ (u + 1) u
    ⟨hu, by linarith⟩).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : u < u + 1)))

theorem zero_iff_bounded_minimumValue (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) :
    (∃ x : X, F x = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → coerciveMinimumValue F G u ≤ B := by
  rw [zero_iff_bounded_coercive_deformation F G hF hFn hGn hcompact]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun u hu => ?_⟩
    obtain ⟨x, hx⟩ := hB u hu
    exact (coerciveMinimumValue_le F G hF hG hFn hcompact x₀ u hu x).trans hx
  · rintro ⟨B, hB⟩
    refine ⟨B, fun u hu => ?_⟩
    obtain ⟨x, hx⟩ := exists_minimizer_of_compact_sublevels F G hF hG hFn hcompact x₀ u hu
    refine ⟨x, ?_⟩
    rw [← coerciveMinimumValue_eq_of_minimizer F G u x hx]
    exact hB u hu

end LeanCanny.CountingHierarchy
