/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.LocalPolynomialRootBound
public import Mathlib.Topology.Order.IntermediateValue

/-! # Local constancy of eventual signs on fixed-degree pieces -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter Set
open scoped Topology Classical

theorem positive_iff_positive_on_zero_free_ray (f : ℝ → ℝ) (R v : ℝ) (hv : R ≤ v)
    (hc : ContinuousOn f (Ici R)) (hz : ∀ u : ℝ, R ≤ u → f u ≠ 0) :
    (0 < f R ↔ 0 < f v) := by
  have hcc : ContinuousOn f (Icc R v) := hc.mono (fun _ h => h.1)
  constructor
  · intro hR
    by_contra hn
    obtain ⟨u, hu, he⟩ := intermediate_value_Icc' hv hcc ⟨le_of_not_gt hn, hR.le⟩
    exact hz u hu.1 he
  · intro hvp
    by_contra hn
    obtain ⟨u, hu, he⟩ := intermediate_value_Icc hv hcc ⟨le_of_not_gt hn, hvp.le⟩
    exact hz u hu.1 he

variable {A : Type*} [TopologicalSpace A]

/-- A continuous sign test whose zeros are controlled by a polynomial family
has a locally constant eventual sign on any fixed-degree piece. The eventual
positive and negative alternatives are supplied by the branch growth test. -/
theorem eventualSign_isClopen_on_degree_piece (P : A → Polynomial ℝ) (d : ℕ)
    (hcoeff : ∀ i, Continuous (fun x => (P x).coeff i))
    (hdegree : ∀ x, (P x).natDegree ≤ d) (hlead : ∀ x, (P x).coeff d ≠ 0)
    (f : A → ℝ → ℝ) (hf : Continuous (fun q : A × ℝ => f q.1 q.2)) (G : A → Prop)
    (hzero : ∀ x v, f x v = 0 → (P x).eval v = 0)
    (hpos : ∀ x, G x → ∀ᶠ v : ℝ in atTop, 0 < f x v)
    (hneg : ∀ x, ¬G x → ∀ᶠ v : ℝ in atTop, f x v < 0) :
    IsClopen {x | G x} := by
  have hclass (x : A) (R : ℝ) (havoid : ∀ v : ℝ, R ≤ v → f x v ≠ 0) :
      G x ↔ 0 < f x R := by
    have hc : ContinuousOn (f x) (Ici R) :=
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
    constructor
    · intro hx
      obtain ⟨v, hv, hfv⟩ := ((eventually_ge_atTop R).and (hpos x hx)).exists
      exact (positive_iff_positive_on_zero_free_ray (f x) R v hv hc havoid).mpr hfv
    · intro hx
      by_contra hn
      obtain ⟨v, hv, hfv⟩ := ((eventually_ge_atTop R).and (hneg x hn)).exists
      have hp := (positive_iff_positive_on_zero_free_ray (f x) R v hv hc havoid).mp hx
      linarith
  have hlocal (x : A) : ∀ᶠ y in 𝓝 x, G y ↔ G x := by
    obtain ⟨R, _, hR⟩ := exists_local_polynomial_root_bound P d hcoeff hdegree hlead x
    have hav : ∀ᶠ y in 𝓝 x, ∀ v : ℝ, R ≤ v → f y v ≠ 0 := by
      filter_upwards [hR] with y hy v hv he
      exact hy v hv (hzero y v he)
    have hxav : ∀ v : ℝ, R ≤ v → f x v ≠ 0 := hav.self_of_nhds
    have hfx : f x R ≠ 0 := hxav R le_rfl
    have hcf : Continuous (fun y => f y R) := hf.comp (continuous_id.prodMk continuous_const)
    by_cases hx : G x
    · have hp : 0 < f x R := (hclass x R hxav).mp hx
      have hnear : ∀ᶠ y in 𝓝 x, 0 < f y R := hcf.continuousAt.eventually (Ioi_mem_nhds hp)
      filter_upwards [hav, hnear] with y hy hposy
      exact iff_of_true ((hclass y R hy).mpr hposy) hx
    · have hn : f x R < 0 := lt_of_le_of_ne (le_of_not_gt (fun h => hx ((hclass x R hxav).mpr h))) hfx
      have hnear : ∀ᶠ y in 𝓝 x, f y R < 0 := hcf.continuousAt.eventually (Iio_mem_nhds hn)
      filter_upwards [hav, hnear] with y hy hnegy
      exact iff_of_false (fun h => (not_lt_of_ge hnegy.le) ((hclass y R hy).mp h)) hx
  have hopen : IsOpen {x | G x} := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    exact (hlocal x).mono (fun y hy => hy.mpr hx))
  have hopenC : IsOpen {x | ¬G x} := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    exact (hlocal x).mono (fun y hy hgy => hx (hy.mp hgy)))
  exact ⟨by simpa only [Set.compl_ofPred, not_not] using hopenC.isClosed_compl, hopen⟩

end LeanCanny.CountingHierarchy
