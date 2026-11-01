/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
/-! # Complete anchored arcs in the literal frozen physical critical fibers -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedPhysicalArcs
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedCriticalArcs
open IntegralMixedSelectedCriticalCuts IntegralMixedSelectedPhysicalFiber
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def AnchoredPhysical (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a b : ℝ) (t₀ : Ioo a b) : Prop :=
    Finite (physical x hm r φ t₀.val) ∧
    ∃ curve : physical x hm r φ t₀.val → ℝ → Fin (n+1) → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → curve j t ∈ physical x hm r φ t) ∧
      (∀ t : Ioo a b, ∀ y, y ∈ physical x hm r φ t.val ↔ ∃! j, curve j t.val = y) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t,curve j t)) '' Ioo a b)

theorem physical_arcs_of_anchored (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a b : ℝ) (t₀ : Ioo a b)
    (H : Anchored x hm r φ a b t₀) : AnchoredPhysical x hm r φ a b t₀ := by
  obtain ⟨Hfinite, curve, Hanchor, Hcont, Hroot, Hcomplete, _⟩ := H
  let : Finite (Fiber x hm r φ t₀.val) := Hfinite
  let e := homeomorph x hm r φ t₀.val
  let lifted : physical x hm r φ t₀.val → ℝ → Fin (n+1) → ℝ :=
    fun j t => IntegralMixedSweepRows.point x hm r φ t (curve (e.symm j) t)
  have Hcontinuous (j : physical x hm r φ t₀.val) : ContinuousOn (lifted j) (Icc a b) :=
    (point_continuous x hm r φ).comp_continuousOn (continuous_id.continuousOn.prodMk (Hcont (e.symm j)))
  have Hphysical (j : physical x hm r φ t₀.val) (t : ℝ) (ht : t ∈ Icc a b) : lifted j t ∈ physical x hm r φ t :=
    ⟨fun i hi => point_frozen x hm r φ t (curve (e.symm j) t) i hi,
      (original_zero_iff x hm r φ t _).mp (Hroot (e.symm j) t ht)⟩
  refine ⟨finite_fiber x hm r φ t₀.val, lifted, ?_, Hcontinuous, Hphysical, ?_, ?_⟩
  · intro j
    change IntegralMixedSweepRows.point x hm r φ t₀.val (curve (e.symm j) t₀.val) = j.val
    rw [Hanchor]
    exact congrArg Subtype.val (e.apply_symm_apply j)
  · intro t y
    constructor
    · intro hy
      have Hy : original x hm r φ (t.val,freeCoordinates r y) = 0 :=
        (original_zero_iff x hm r φ t.val _).mpr (by rw [reconstruct x hm r φ t.val y hy.1]; exact hy.2)
      obtain ⟨j, Hj, Huniq⟩ := (Hcomplete t (freeCoordinates r y)).mp Hy
      refine ⟨e j, ?_, ?_⟩
      · change IntegralMixedSweepRows.point x hm r φ t.val (curve (e.symm (e j)) t.val) = y
        rw [e.symm_apply_apply, Hj, reconstruct x hm r φ t.val y hy.1]
      · intro k Hk
        have HK := congrArg (freeCoordinates r) Hk
        change freeCoordinates r (IntegralMixedSweepRows.point x hm r φ t.val (curve (e.symm k) t.val)) = _ at HK
        rw [free_point] at HK
        have HE := congrArg e (Huniq (e.symm k) HK)
        simpa only [e.apply_symm_apply] using HE
    · rintro ⟨j, Hj, _⟩
      rw [← Hj]
      exact Hphysical j t.val (Ioo_subset_Icc_self t.property)
  · intro j
    exact FrontierCover.accessible_open_arc (continuous_id.continuousOn.prodMk (Hcontinuous j))

theorem anchored_physical_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : IntegralMixedRelativeCuts.Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b) (havoid : ∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) : AnchoredPhysical x hm r φ a b t₀ :=
  physical_arcs_of_anchored x hm r φ a b t₀ (IntegralMixedSelectedCriticalCuts.anchored_arcs x hm r φ c a b t₀ havoid)

theorem exists_anchored_physical_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ c : IntegralMixedRelativeCuts.Choices x hm r φ, (bad x hm r φ c).Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
      (∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) → AnchoredPhysical x hm r φ a b t₀ := by
  obtain ⟨c, Hc, _⟩ := IntegralMixedSelectedCriticalCuts.exists_anchored_arcs x hm r φ
  exact ⟨c, Hc, fun a b t₀ => anchored_physical_arcs x hm r φ c a b t₀⟩

end LeanCanny.Connectivity.IntegralMixedSelectedPhysicalArcs
