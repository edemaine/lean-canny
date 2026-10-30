/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWordPersistence

/-! # Descriptor identities at one fixed algebraic sample

These lemmas eliminate auxiliary tuple choices at a shared sample. A complete
geometric fiber supplies only correctness data; the native word writer still
uses the original equations and complete labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRankWord
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem current_in_fiber (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w) :
    currentValue F cone height s w ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s
      (sampleValue F cone height s w) := by
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  simp only [currentValue, sampleValue, anchorPoint_packet F cone height s w hw]
  intro i
  exact H.2.2 (0 : Fin 3) i

theorem view_at_sample {J : Type*} (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) (t : ℝ)
    (hroot : ∀ k, points s t k ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t)
    (hcover : ∀ x, x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t → ∃ k, points s t k = x)
    (hT : sampleValue F cone height s w = t)
    (hX : currentValue F cone height s w = points s t j) : BranchView F cone height points j s w := by
  unfold BranchView
  rw [hT]
  exact ⟨hroot, hcover, hX⟩

theorem word_eq_of_same_sample_branch {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w v : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : BranchView F cone height points j s w) (hV : BranchView F cone height points j s v)
    (ht : sampleValue F cone height s w = sampleValue F cone height s v) :
    word F cone height (pair s w) = word F cone height (pair s v) := by
  rw [word_packet_pair F cone height points j s w hs hw hW,
    word_packet_pair F cone height points j s v hs hv hV]
  unfold branchWord branchOrdinal
  rw [ht]

end LeanCanny.Encoding.FlatAffineEndpointRankWord
