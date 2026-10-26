/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CircleSublevelLift

/-! # Exact path preservation for circle slack variables

Circle fibers are path connected, including the radius-zero singleton. The
continuous section and paths inside each fiber therefore preserve `Joined`
for all points of the lift, without any local path connectivity assumption
on the original sublevel.
-/

@[expose] public section
namespace LeanCanny.Geometry.CircleSublevelLift
open Set Complex

variable {X : Type*} [TopologicalSpace X]

theorem fiber_pathConnected (g : X → ℝ) (e : ℝ) (x : Base g e) :
    IsPathConnected ((projection g e) ⁻¹' {x}) := by
  apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
  rw [fiber_image]
  exact (isPathConnected_sphere (E := ℂ) (by simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])
    (0 : ℂ) (Real.sqrt_nonneg (e - g x.val))).image (continuous_const.prodMk continuous_id)

theorem joined_section (g : X → ℝ) (e : ℝ) (p : Total g e) :
    Joined p (sectionMap g e (projection g e p)) :=
  ((fiber_pathConnected g e (projection g e p)).joinedIn p rfl
    (sectionMap g e (projection g e p)) (projection_section g e _)).joined

theorem joined_iff (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p q : Total g e) :
    Joined p q ↔ Joined (projection g e p) (projection g e q) := by
  constructor
  · intro h
    exact h.map (continuous_projection g e)
  · intro h
    exact (joined_section g e p).trans ((h.map (continuous_section g hg e)).trans (joined_section g e q).symm)

theorem pathComponent_preimage (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p : Total g e) :
    (projection g e) ⁻¹' pathComponent (projection g e p) = pathComponent p := by
  ext q
  exact (joined_iff g hg e p q).symm

theorem section_joined_iff (g : X → ℝ) (hg : Continuous g) (e : ℝ) (x y : Base g e) :
    Joined (sectionMap g e x) (sectionMap g e y) ↔ JoinedIn (Base g e) x.val y.val := by
  rw [joined_iff g hg e, projection_section, projection_section]
  exact (joinedIn_iff_joined x.property y.property).symm

end LeanCanny.Geometry.CircleSublevelLift
