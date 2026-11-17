/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoerciveMinimumValue

/-! # Joint continuity of parameterized coercive minimum values

A fixed function with compact sublevel sets bounds every objective from below.
Near each parameter, comparison with one fixed point confines all minimizers
to the same compact set. This is the continuity step for parameterized fibers.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Set Filter
open scoped Topology

variable {A X : Type*} [TopologicalSpace A] [MetricSpace X]

noncomputable def parameterMinimumValue (H : A → X → ℝ) (p : A) : ℝ := sInf (range (H p))

theorem exists_parameter_minimizer (H : A → X → ℝ) (G : X → ℝ)
    (hH : Continuous (fun q : A × X => H q.1 q.2)) (hG : Continuous G)
    (hdom : ∀ p x, G x ≤ H p x) (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B})
    (x₀ : X) (p : A) : ∃ x, IsMinOn (H p) univ x := by
  have hc : Continuous (H p) := hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x, hx⟩ := exists_minimizer_of_compact_sublevels
    (fun x => H p x - G x) G (hc.sub hG) hG (fun x => sub_nonneg.mpr (hdom p x))
    hcompact x₀ 1 (by norm_num)
  refine ⟨x, ?_⟩
  simpa only [one_mul, add_sub_cancel] using hx

omit [TopologicalSpace A] [MetricSpace X] in
theorem parameterMinimumValue_eq (H : A → X → ℝ) (p : A) (x : X)
    (hx : IsMinOn (H p) univ x) : parameterMinimumValue H p = H p x := by
  apply IsLeast.csInf_eq
  refine ⟨mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hx (mem_univ y)

/-- The minimum is jointly continuous in every parameter, including boundary
parameters when they are supplied as a subtype such as the nonnegative reals. -/
theorem parameterMinimumValue_continuous (H : A → X → ℝ) (G : X → ℝ)
    (hH : Continuous (fun q : A × X => H q.1 q.2)) (hG : Continuous G)
    (hdom : ∀ p x, G x ≤ H p x) (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B})
    (x₀ : X) : Continuous (parameterMinimumValue H) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let B := H p₀ x₀ + 1
  let S := {x | G x ≤ B}
  have hc : Continuous (fun p => sInf ((H p) '' S)) := (hcompact B).continuous_sInf hH
  have hb : ∀ᶠ p in 𝓝 p₀, H p x₀ < B :=
    (hH.comp (continuous_id.prodMk continuous_const)).continuousAt.eventually
      (Iio_mem_nhds (lt_add_one (H p₀ x₀)))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hb] with p hp
  obtain ⟨x, hx⟩ := exists_parameter_minimizer H G hH hG hdom hcompact x₀ p
  have hxS : x ∈ S := (hdom p x).trans ((hx (mem_univ x₀)).trans hp.le)
  have he : sInf ((H p) '' S) = H p x := by
    apply IsLeast.csInf_eq
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact hx (mem_univ y)
  exact (parameterMinimumValue_eq H p x hx).trans he.symm

end LeanCanny.CountingHierarchy
