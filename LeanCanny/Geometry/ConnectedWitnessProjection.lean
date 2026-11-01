/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Connected.PathConnected
/-! # A continuous section with paths inside every witness fiber preserves components -/
@[expose] public section
namespace LeanCanny.Geometry.ConnectedWitnessProjection
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : Y → X) (s : X → Y) (hp : Continuous p) (hs : Continuous s)
  (Hps : Function.LeftInverse p s) (HF : ∀ y, JoinedIn univ y (s (p y)))

include hp hs HF in
theorem joined_iff (y z : Y) : JoinedIn univ y z ↔ JoinedIn univ (p y) (p z) := by
  constructor
  · intro H
    exact (H.map hp.continuousOn).mono (subset_univ _)
  · intro H
    have HS := (H.map hs.continuousOn).mono (subset_univ _)
    exact (HF y).trans (HS.trans (HF z).symm)

include hp hs Hps HF in
theorem preconnected_iff : IsPreconnected (univ : Set Y) ↔ IsPreconnected (univ : Set X) := by
  constructor
  · intro H
    have HE : p '' (univ : Set Y) = univ := by
      ext x
      constructor
      · intro _; trivial
      · intro _; exact ⟨s x,mem_univ _,Hps x⟩
    rw [← HE]
    exact H.image p hp.continuousOn
  · intro H
    have HR : IsPreconnected (range s) := by
      simpa only [image_univ] using H.image s hs.continuousOn
    apply isPreconnected_of_forall_pair
    intro y _ z _
    obtain ⟨γ,_⟩ := HF y
    obtain ⟨δ,_⟩ := HF z
    have HG := isPreconnected_range γ.continuous
    have HD := isPreconnected_range δ.continuous
    have HG' : IsPreconnected (range s ∪ range γ) := HR.union (s (p y)) (mem_range_self _)
      γ.target_mem_range HG
    have HD' : IsPreconnected ((range s ∪ range γ) ∪ range δ) := HG'.union (s (p z))
      (Or.inl (mem_range_self _)) δ.target_mem_range HD
    exact ⟨_,subset_univ _,Or.inl (Or.inr γ.source_mem_range),Or.inr δ.source_mem_range,HD'⟩

end LeanCanny.Geometry.ConnectedWitnessProjection
