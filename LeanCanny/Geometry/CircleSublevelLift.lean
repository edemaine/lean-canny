/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Linarith

/-! # Connected circle fibers for sublevel lifting

The level equation g(x) + u² + v² = e projects onto g(x) ≤ e. Its fibers are
circles, including the radius-zero singleton, and it has a continuous section.
The constructed quotient map therefore preserves exact connected components.
No regularity or path connectivity of the original sublevel is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.CircleSublevelLift
open Set Complex

variable {X : Type*} [TopologicalSpace X]

def Base (g : X → ℝ) (e : ℝ) := {x : X | g x ≤ e}
def Total (g : X → ℝ) (e : ℝ) := {p : X × ℂ | g p.1 + Complex.normSq p.2 = e}

def projection (g : X → ℝ) (e : ℝ) (p : Total g e) : Base g e :=
  ⟨p.val.1, by
    change g p.val.1 ≤ e
    have hn := Complex.normSq_nonneg p.val.2
    have hp := p.property
    change g p.val.1 + Complex.normSq p.val.2 = e at hp
    linarith⟩

noncomputable def sectionMap (g : X → ℝ) (e : ℝ) (x : Base g e) : Total g e :=
  ⟨(x.val, (Real.sqrt (e - g x.val) : ℂ)), by
    change g x.val + Complex.normSq (Real.sqrt (e - g x.val) : ℂ) = e
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.mpr x.property)]
    ring⟩

omit [TopologicalSpace X] in
theorem projection_section (g : X → ℝ) (e : ℝ) (x : Base g e) :
    projection g e (sectionMap g e x) = x := rfl

theorem continuous_projection (g : X → ℝ) (e : ℝ) : Continuous (projection g e) :=
  Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _

theorem continuous_section (g : X → ℝ) (hg : Continuous g) (e : ℝ) : Continuous (sectionMap g e) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (continuous_const.sub (hg.comp continuous_subtype_val))))

theorem quotient_projection (g : X → ℝ) (hg : Continuous g) (e : ℝ) :
    Topology.IsQuotientMap (projection g e) :=
  Topology.IsQuotientMap.of_inverse (continuous_section g hg e) (continuous_projection g e)
    (projection_section g e)

omit [TopologicalSpace X] in
theorem fiber_image (g : X → ℝ) (e : ℝ) (x : Base g e) :
    Subtype.val '' ((projection g e) ⁻¹' {x}) =
      (fun z : ℂ => (x.val, z)) '' Metric.sphere 0 (Real.sqrt (e - g x.val)) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : projection g e z = x := hz
    have hx : z.val.1 = x.val := congrArg Subtype.val hz'
    have hs : ‖z.val.2‖ ^ 2 = e - g x.val := by
      rw [← Complex.normSq_eq_norm_sq]
      have hp := z.property
      change g z.val.1 + Complex.normSq z.val.2 = e at hp
      rw [hx] at hp
      linarith
    refine ⟨z.val.2, ?_, Prod.ext hx.symm rfl⟩
    simp only [Metric.mem_sphere, dist_zero_right]
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  · rintro ⟨z, hz, rfl⟩
    have hn : ‖z‖ = Real.sqrt (e - g x.val) := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hs : Complex.normSq z = e - g x.val := by
      rw [Complex.normSq_eq_norm_sq, hn, Real.sq_sqrt (sub_nonneg.mpr x.property)]
    refine ⟨⟨(x.val, z), ?_⟩, rfl, rfl⟩
    change g x.val + Complex.normSq z = e
    rw [hs]
    ring

theorem fiber_connected (g : X → ℝ) (e : ℝ) (x : Base g e) :
    IsConnected ((projection g e) ⁻¹' {x}) := by
  have hc := isConnected_sphere (E := ℂ) (by simp only [Complex.rank_real_complex, Nat.one_lt_ofNat]) (0 : ℂ)
    (Real.sqrt_nonneg (e - g x.val))
  refine ⟨⟨sectionMap g e x, projection_section g e x⟩, ?_⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  rw [fiber_image]
  exact hc.isPreconnected.image _ (continuous_const.prodMk continuous_id).continuousOn

theorem component_preimage (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p : Total g e) :
    (projection g e) ⁻¹' connectedComponent (projection g e p) = connectedComponent p :=
  (quotient_projection g hg e).isCoinducing.preimage_connectedComponent (fiber_connected g e) p

theorem mem_component_iff (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p q : Total g e) :
    q ∈ connectedComponent p ↔ projection g e q ∈ connectedComponent (projection g e p) := by
  rw [← component_preimage g hg e p]
  rfl

theorem section_component_iff (g : X → ℝ) (hg : Continuous g) (e : ℝ) (x y : Base g e) :
    sectionMap g e y ∈ connectedComponent (sectionMap g e x) ↔
      y.val ∈ connectedComponentIn (Base g e) x.val := by
  rw [mem_component_iff g hg e, projection_section, projection_section,
    connectedComponentIn_eq_image x.property]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, he⟩
    have he' : z = y := Subtype.ext he
    exact he' ▸ hz

theorem preconnected_iff (g : X → ℝ) (hg : Continuous g) (e : ℝ) :
    IsPreconnected (Total g e) ↔ IsPreconnected (Base g e) := by
  rw [isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace,
    preconnectedSpace_iff_connectedComponent, preconnectedSpace_iff_connectedComponent]
  constructor
  · intro h x
    apply eq_univ_of_univ_subset
    intro y _
    have hm : sectionMap g e y ∈ connectedComponent (sectionMap g e x) := by
      rw [h _]
      exact mem_univ _
    simpa only [projection_section] using
      (mem_component_iff g hg e (sectionMap g e x) (sectionMap g e y)).mp hm
  · intro h p
    apply eq_univ_of_univ_subset
    intro q _
    apply (mem_component_iff g hg e p q).mpr
    rw [h _]
    exact mem_univ _

end LeanCanny.Geometry.CircleSublevelLift
