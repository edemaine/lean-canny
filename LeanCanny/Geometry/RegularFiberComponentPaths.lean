/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.RegularFiber
/-! # Ambient component membership gives paths in a locally path connected fiber -/
@[expose] public section
namespace LeanCanny.Geometry.RegularFiberComponentPaths
open Set

theorem joinedIn_of_component {X : Type*} [TopologicalSpace X] (S : Set X) [LocallyPathConnectedSpace S]
    (y : X) (hy : y ∈ S) (z : X) (hz : z ∈ connectedComponentIn S y) : JoinedIn S y z := by
  rw [connectedComponentIn_eq_image hy] at hz
  obtain ⟨w,HW,rfl⟩ := hz
  apply (joinedIn_iff_joined hy w.property).mpr
  exact (connectedComponent_eq_iff_joined _ _).mp (connectedComponent_eq HW)

end LeanCanny.Geometry.RegularFiberComponentPaths
