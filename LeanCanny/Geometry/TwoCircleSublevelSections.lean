/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TwoCircleSublevelMap
public import Mathlib.Topology.Connected.PathConnected
/-! # Explicit sections retain paths through both sublevel constraints -/
@[expose] public section
namespace LeanCanny.Geometry.TwoCircleSublevelSections
open Set
variable {X : Type*} [TopologicalSpace X]

def Window (g h : X → ℝ) (e r : ℝ) : Set X := {x | h x ≤ r ∧ g x ≤ e}
noncomputable def point (g h : X → ℝ) (e r : ℝ) (x : X) : X × (ℂ × ℂ) :=
  (x,((Real.sqrt (e-g x) : ℂ),(Real.sqrt (r-h x) : ℂ)))

theorem continuous_point (g h : X → ℝ) (hg : Continuous g) (hh : Continuous h) (e r : ℝ) :
    Continuous (point g h e r) :=
  continuous_id.prodMk ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.sub hg))).prodMk
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.sub hh))))

omit [TopologicalSpace X] in
theorem point_level (g h : X → ℝ) (e r : ℝ) (x : X) (hx : x ∈ Window g h e r) :
    TwoCircleSublevelMap.energy g h (point g h e r x) = (e,r) := by
  apply Prod.ext
  · change g x + Complex.normSq (Real.sqrt (e-g x) : ℂ) = e
    rw [Complex.normSq_ofReal,Real.mul_self_sqrt (sub_nonneg.mpr hx.2)]
    ring
  · change h x + Complex.normSq (Real.sqrt (r-h x) : ℂ) = r
    rw [Complex.normSq_ofReal,Real.mul_self_sqrt (sub_nonneg.mpr hx.1)]
    ring

omit [TopologicalSpace X] in
theorem old_mem (g h : X → ℝ) (e r : ℝ) (p : X × (ℂ × ℂ))
    (hp : TwoCircleSublevelMap.energy g h p = (e,r)) : p.1 ∈ Window g h e r := by
  have H1 : g p.1 + Complex.normSq p.2.1 = e := congrArg Prod.fst hp
  have H2 : h p.1 + Complex.normSq p.2.2 = r := congrArg Prod.snd hp
  constructor
  · linarith [Complex.normSq_nonneg p.2.2]
  · linarith [Complex.normSq_nonneg p.2.1]

theorem joined_iff (g h : X → ℝ) (hg : Continuous g) (hh : Continuous h) (e r : ℝ)
    (x y : X) : JoinedIn (Window g h e r) x y ↔
      JoinedIn ((TwoCircleSublevelMap.energy g h) ⁻¹' {(e,r)}) (point g h e r x) (point g h e r y) := by
  constructor
  · intro H
    apply (H.map (continuous_point g h hg hh e r).continuousOn).mono
    rintro p ⟨a,ha,rfl⟩
    exact point_level g h e r a ha
  · intro H
    have HP := H.map continuous_fst.continuousOn
    change JoinedIn (Prod.fst '' ((TwoCircleSublevelMap.energy g h) ⁻¹' {(e,r)})) x y at HP
    apply HP.mono
    rintro a ⟨p,hp,rfl⟩
    exact old_mem g h e r p hp

end LeanCanny.Geometry.TwoCircleSublevelSections
