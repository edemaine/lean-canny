/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteRankImage

/-! # Native projection ranks agree with persistent geometric branch ranks -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem anchor_allowed (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height (frame c))
    (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c)) :
    pair c (anchor c) ∈ allowed F cone height := by
  apply (allowed_packet F cone height c (anchor c)).mpr
  refine ⟨hs, ?_⟩
  apply (SquareSampleCompletePrefixEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height) (fun _ => 2) (frame c) (anchor c) (anchor c) ha ha (by
      change 2 ≤ FlatAffineEndpointFiniteFrame.arity F (frame c)
      dsimp only [FlatAffineEndpointFiniteFrame.arity, FlatAffineEndpointRows.arity]
      omega)).mpr
  intro i _
  rfl

theorem branch_packet {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (c : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height (frame c))
    (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c))
    (points : J → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c)) → ℝ)
    (hpoints : ∀ j, points j ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (frame c)
      (FlatAffineEndpointFiniteProjection.sample F (frame c)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c) ha).val))
    (hcover : ∀ current, current ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (frame c)
      (FlatAffineEndpointFiniteProjection.sample F (frame c)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c) ha).val) →
      ∃ j, points j = current)
    (j : J) (he : FlatAffineEndpointFiniteProjection.copy F (frame c)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c) ha).val 0 = points j) :
    FiniteWordProjectionRank.rank (data F cone height index) (pair c (anchor c)) =
      AlgebraicFiberImageRank.rank points j (index c) := by
  let D := data F cone height index
  have himage : (FiniteWordProjectionRank.indices D c).image (FiniteWordProjectionRank.projection D c) =
      Finset.univ.image (fun k => points k (index c)) := by
    ext y
    rw [image_iff F cone height index c hs ha y]
    constructor
    · rintro ⟨current, hc, hy⟩
      obtain ⟨k, rfl⟩ := hcover current hc
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hy.symm⟩
    · intro hy
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨points k, hpoints k, rfl⟩
  have hv : D.value c (anchor c) = points j (index c) :=
    (value_packet F cone height index c (anchor c) ha).trans (congrFun he (index c))
  rw [FiniteWordProjectionRank.image_rank D c (anchor c) (anchor_allowed F cone height c hs ha), himage, hv]
  exact (FiniteImageRank.rank_eq Finset.univ (fun k => points k (index c)) (points j (index c))).symm

end LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
