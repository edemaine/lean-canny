/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen

import Mathlib.Topology.Separation.Connected

/-! # Finite connected components form a clopen cover -/

@[expose] public section
namespace LeanCanny.Geometry.FiniteComponentCover
open Set
open scoped Classical
variable {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]

theorem isClopen_component (x : X) : IsClopen (connectedComponent x) := by
  rw [← connectedComponents_preimage_singleton]
  exact (isClopen_discrete _).preimage ConnectedComponents.continuous_coe

end LeanCanny.Geometry.FiniteComponentCover
