/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.OrderedRealCellIncidence

/-! # Incidence in sign-stable subsets of the real line

Relative incidence retains exactly the ambient neighbor edges whose two
cells are present. An excluded endpoint cannot connect the adjacent gaps.
-/

@[expose] public section
namespace LeanCanny.Connectivity.OrderedRealCellRestrictedIncidence
open Set Geometry.OrderedRealCells OrderedRealCellCover OrderedRealCellIncidence
open scoped Classical

theorem subset_of_nonempty (s : Finset ℝ) (S : Set ℝ) (hS : Stable s S) (i : Index s)
    (hi : (restrictedPiece s S i).Nonempty) : piece s i ⊆ S := by
  obtain ⟨x, hx⟩ := hi
  intro y hy
  exact (hS i x.val hx y hy).mp x.property

theorem closure_restricted (s : Finset ℝ) (S : Set ℝ) (i : Index s) (hi : piece s i ⊆ S) :
    closure (restrictedPiece s S i) = ((↑) : S → ℝ) ⁻¹' closure (piece s i) := by
  have him : ((↑) : S → ℝ) '' restrictedPiece s S i = piece s i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hi hx⟩, hx, rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, him]

theorem incident_iff_ambient (s : Finset ℝ) (S : Set ℝ) (i j : Index s)
    (hi : piece s i ⊆ S) (hj : piece s j ⊆ S) :
    FrontierCover.Incident (restrictedPiece s S) i j ↔ FrontierCover.Incident (piece s) i j := by
  simp only [FrontierCover.Incident, closure_restricted s S i hi, closure_restricted s S j hj]
  constructor
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact Or.inl ⟨x.val, hx, hy⟩
    · exact Or.inr ⟨x.val, hx, hy⟩
  · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
    · exact Or.inl ⟨⟨x, hi hx⟩, hx, hy⟩
    · exact Or.inr ⟨⟨x, hj hx⟩, hx, hy⟩

theorem incident_iff (s : Finset ℝ) (S : Set ℝ) (hS : Stable s S) (i j : Index s) :
    FrontierCover.Incident (restrictedPiece s S) i j ↔
      (restrictedPiece s S i).Nonempty ∧ (restrictedPiece s S j).Nonempty ∧ Adjacent s i j := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := h.nonempty (restrictedPiece s S)
    exact ⟨hi, hj, (incident_iff_adjacent s i j).mp
      ((incident_iff_ambient s S i j (subset_of_nonempty s S hS i hi)
        (subset_of_nonempty s S hS j hj)).mp h)⟩
  · rintro ⟨hi, hj, h⟩
    exact (incident_iff_ambient s S i j (subset_of_nonempty s S hS i hi)
      (subset_of_nonempty s S hS j hj)).mpr ((incident_iff_adjacent s i j).mpr h)

end LeanCanny.Connectivity.OrderedRealCellRestrictedIncidence
