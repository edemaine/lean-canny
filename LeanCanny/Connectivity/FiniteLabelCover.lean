/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitFrontierCover

/-! # Extending labeled covers to every fixed-width word

An injectively labeled accessible cover becomes a bit frontier cover by
assigning the empty piece to unused words. Incidence on the resulting cover
is exactly incidence between the uniquely labeled original pieces.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FiniteLabelCover
open Set
open scoped Classical
variable {ι X : Type*}

def piece (label : ι → List Bool) (original : ι → Set X) (word : List Bool) : Set X :=
  {x | ∃ i, label i = word ∧ x ∈ original i}

theorem piece_label (label : ι → List Bool) (hl : Function.Injective label) (original : ι → Set X) (i : ι) :
    piece label original (label i) = original i := by
  ext x
  constructor
  · rintro ⟨j, hj, hx⟩
    exact hl hj ▸ hx
  · intro hx
    exact ⟨i, rfl, hx⟩

theorem piece_empty (label : ι → List Bool) (original : ι → Set X) (word : List Bool)
    (hw : ¬ ∃ i, label i = word) : piece label original word = ∅ := by
  ext x
  constructor
  · rintro ⟨i, hi, _⟩
    exact (hw ⟨i, hi⟩).elim
  · intro hx
    exact hx.elim

theorem nonempty_iff (label : ι → List Bool) (original : ι → Set X) (word : List Bool) :
    (piece label original word).Nonempty ↔ ∃ i, label i = word ∧ (original i).Nonempty := by
  constructor
  · rintro ⟨x, i, hi, hx⟩
    exact ⟨i, hi, x, hx⟩
  · rintro ⟨i, hi, x, hx⟩
    exact ⟨x, i, hi, hx⟩

variable [TopologicalSpace X]

theorem accessible (label : ι → List Bool) (hl : Function.Injective label) (original : ι → Set X)
    (ha : ∀ i, FrontierCover.Accessible (original i)) (word : List Bool) :
    FrontierCover.Accessible (piece label original word) := by
  by_cases hw : ∃ i, label i = word
  · obtain ⟨i, rfl⟩ := hw
    rw [piece_label label hl]
    exact ha i
  · rw [piece_empty label original word hw]
    intro x hx
    simp only [closure_empty, mem_empty_iff_false] at hx

theorem incident_iff (label : ι → List Bool) (hl : Function.Injective label) (original : ι → Set X) (u v : List Bool) :
    FrontierCover.Incident (piece label original) u v ↔
      ∃ i j, label i = u ∧ label j = v ∧ FrontierCover.Incident original i j := by
  constructor
  · intro h
    obtain ⟨hi, hj⟩ := h.nonempty (piece label original)
    obtain ⟨i, rfl, _⟩ := (nonempty_iff label original u).mp hi
    obtain ⟨j, rfl, _⟩ := (nonempty_iff label original v).mp hj
    refine ⟨i, j, rfl, rfl, ?_⟩
    simpa only [FrontierCover.Incident, piece_label label hl] using h
  · rintro ⟨i, j, rfl, rfl, h⟩
    simpa only [FrontierCover.Incident, piece_label label hl] using h

noncomputable def cover (w : ℕ) (label : ι → List Bool) (hl : Function.Injective label)
    (hw : ∀ i, (label i).length = w) (original : ι → Set X)
    (hc : ∀ x, ∃ i, x ∈ original i) (ha : ∀ i, FrontierCover.Accessible (original i))
    (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool)
    (hv : ∀ word, valid word = true ↔ ∃ i, label i = word ∧ (original i).Nonempty)
    (he : ∀ u v, edge u v = true ↔ ∃ i j, label i = u ∧ label j = v ∧ FrontierCover.Incident original i j) :
    BitFrontierCover X w edge valid where
  piece word := piece label original word.val
  cover x := by
    obtain ⟨i, hi⟩ := hc x
    exact ⟨⟨label i, hw i⟩, i, rfl, hi⟩
  accessible word := accessible label hl original ha word.val
  valid_iff word := (hv word.val).trans (nonempty_iff label original word.val).symm
  edge_iff u v := (he u.val v.val).trans (incident_iff label hl original u.val v.val).symm

end LeanCanny.Connectivity.FiniteLabelCover
