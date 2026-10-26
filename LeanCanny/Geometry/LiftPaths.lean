/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CircleSublevelPaths
public import LeanCanny.Geometry.PurePowerSublevelLift
public import LeanCanny.Geometry.BoundedZeroComponents

/-! # Paths in the pure-power and bounded zero lifts

The actual coordinate homeomorphisms transfer circle-fiber path preservation.
This concerns the exact sublevel or bounded zero set being lifted. It does
not recover paths in a singular zero set from paths in a positive sublevel.
-/

@[expose] public section
namespace LeanCanny.Geometry
open Set

theorem joined_homeomorph_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (x y : X) : Joined (h x) (h y) ↔ Joined x y := by
  constructor
  · intro hxy
    simpa only [Homeomorph.symm_apply_apply] using hxy.map h.symm.continuous
  · intro hxy
    exact hxy.map h.continuous

namespace PurePowerSublevelLift
variable {X : Type*} [TopologicalSpace X]

theorem joined_iff (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p q : Total m g e) :
    Joined p q ↔ Joined (projection m hm g e p) (projection m hm g e q) := by
  rw [← joined_homeomorph_iff (levelHomeomorph m hm g e) p q, CircleSublevelLift.joined_iff g hg e]
  rfl

theorem pathComponent_preimage (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p : Total m g e) :
    (projection m hm g e) ⁻¹' pathComponent (projection m hm g e p) = pathComponent p := by
  ext q
  exact (joined_iff m hm g hg e p q).symm

theorem section_joined_iff (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ)
    (x y : CircleSublevelLift.Base g e) :
    Joined (sectionMap m hm g e x) (sectionMap m hm g e y) ↔
      JoinedIn (CircleSublevelLift.Base g e) x.val y.val := by
  rw [joined_iff m hm g hg e, projection_section, projection_section]
  exact (joinedIn_iff_joined x.property y.property).symm

end PurePowerSublevelLift

namespace BoundedZeroSource
open MvPolynomial
variable {n : ℕ}

theorem joined_iff (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (u v : Zeros q R) :
    Joined u v ↔ Joined (projection q R u) (projection q R v) := by
  rw [← joined_homeomorph_iff (zeroHomeomorph q R) u v,
    CircleSublevelLift.joined_iff (radialOn q) (continuous_radialOn q) (radiusSquared R : ℝ)]
  exact (joined_homeomorph_iff (baseHomeomorph q R) _ _).symm

theorem pathComponent_preimage (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (u : Zeros q R) :
    (projection q R) ⁻¹' pathComponent (projection q R u) = pathComponent u := by
  ext v
  exact (joined_iff q R u v).symm

theorem section_joined_iff (q : MvPolynomial (Fin n) ℤ) (R : ℕ) (x y : Bounded q R) :
    Joined (sectionMap q R x) (sectionMap q R y) ↔ JoinedIn (Bounded q R) x.val y.val := by
  rw [joined_iff q R, projection_section, projection_section]
  exact (joinedIn_iff_joined x.property y.property).symm

end BoundedZeroSource
end LeanCanny.Geometry
