/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitFrontierCover

/-! # Accessible bit covers from closed path covers -/

@[expose] public section
namespace LeanCanny.Connectivity.BitPathCover
open Set
open scoped Classical
variable {X : Type*} [TopologicalSpace X] {w : ℕ}
  {edge : List Bool → List Bool → Bool} {valid : List Bool → Bool}

def toFrontier (C : BitPathCover X w edge valid) : BitFrontierCover X w edge valid where
  piece := C.piece
  cover := C.cover
  accessible i := by
    intro x hx y hy
    have HX : x ∈ C.piece i := (C.closed i).closure_eq ▸ hx
    simpa only [insert_eq_of_mem HX] using C.paths i x HX y hy
  valid_iff := C.valid_iff
  edge_iff i j := by
    rw [C.edge_iff, FrontierCover.Incident, (C.closed i).closure_eq, (C.closed j).closure_eq]
    exact ⟨Or.inl, fun H => H.elim id (fun ⟨x, hx, hy⟩ => ⟨x, hy, hx⟩)⟩

end LeanCanny.Connectivity.BitPathCover
