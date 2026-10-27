/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Constructions

/-! # Connectivity in a coordinate line

Updating one coordinate embeds the real line in tuple space. Restricting any
set to that line preserves both preconnectedness and paths exactly.
-/

@[expose] public section
namespace LeanCanny.Geometry.CoordinateLine
open Set Topology
variable {ι : Type*} [DecidableEq ι]

def piece (S : Set (ι → ℝ)) (x : ι → ℝ) (j : ι) : Set (ι → ℝ) :=
  {y | y ∈ S ∧ ∀ i, i ≠ j → y i = x i}

theorem update_isEmbedding (x : ι → ℝ) (j : ι) :
    IsEmbedding (fun t : ℝ => Function.update x j t) := by
  have hc : Continuous (fun t : ℝ => Function.update x j t) :=
    continuous_const.update j continuous_id
  apply IsEmbedding.of_comp hc (continuous_apply j)
  have he : (fun y : ι → ℝ => y j) ∘ (fun t : ℝ => Function.update x j t) = id := by
    funext t
    exact Function.update_self j t x
  rw [he]
  exact IsEmbedding.id

theorem image_parameterSet (S : Set (ι → ℝ)) (x : ι → ℝ) (j : ι) :
    (fun t : ℝ => Function.update x j t) '' {t | Function.update x j t ∈ S} = piece S x j := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, fun i hi => Function.update_of_ne hi t x⟩
  · rintro ⟨hy, hx⟩
    have he : Function.update x j (y j) = y := by
      funext i
      by_cases hi : i = j
      · subst i
        exact Function.update_self j (y j) x
      · rw [Function.update_of_ne hi, hx i hi]
    refine ⟨y j, ?_, he⟩
    change Function.update x j (y j) ∈ S
    rw [he]
    exact hy

theorem preconnected_iff (S : Set (ι → ℝ)) (x : ι → ℝ) (j : ι) :
    IsPreconnected (piece S x j) ↔ IsPreconnected {t : ℝ | Function.update x j t ∈ S} := by
  rw [← image_parameterSet]
  exact (update_isEmbedding x j).isInducing.isPreconnected_image

theorem joinedIn_iff (S : Set (ι → ℝ)) (x : ι → ℝ) (j : ι) (s t : ℝ)
    (hs : Function.update x j s ∈ S) (ht : Function.update x j t ∈ S) :
    JoinedIn (piece S x j) (Function.update x j s) (Function.update x j t) ↔
      JoinedIn {r : ℝ | Function.update x j r ∈ S} s t := by
  rw [← image_parameterSet]
  exact (update_isEmbedding x j).isInducing.joinedIn_image hs ht

end LeanCanny.Geometry.CoordinateLine
