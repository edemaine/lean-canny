/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
public import LeanCanny.Geometry.AlgebraicFiberImageRank

/-! # The filtered joint-label image is the actual spatial fiber image

Every admitted label projects to an original solution at the anchor's sample
height. Conversely every original solution lifts with the anchor's endpoint
copies and receives an admitted complete label. Thus no extraneous coordinate
annihilator roots enter the distinct projection rank.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem value_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) w) :
    (data F cone height index).value c w = FlatAffineEndpointFiniteProjection.copy F (frame c)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) w hw).val 0 (index c) := by
  change SquareSampleCompleteProjectionRank.valueAt (FlatAffineEndpointFiniteSample.input F cone height) frame (coordinate F index) c w = _
  rw [SquareSampleCompleteProjectionRank.valueAt, dite_eq_left hw]
  rfl

theorem image_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (c : List Bool) → Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c))) (c : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height (frame c))
    (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c)) (y : ℝ) :
    y ∈ (FiniteWordProjectionRank.indices (data F cone height index) c).image
      (FiniteWordProjectionRank.projection (data F cone height index) c) ↔
    ∃ current : Fin (FlatAffineEndpointFiniteSide.originalCount F (frame c)) → ℝ,
      current ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (frame c)
        (FlatAffineEndpointFiniteProjection.sample F (frame c)
          (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (frame c) (anchor c) ha).val) ∧
        y = current (index c) := by
  let D := data F cone height index
  let I := FlatAffineEndpointFiniteSample.input F cone height
  let s := frame c
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate I s (anchor c) ha).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate I s (anchor c) ha).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  constructor
  · intro hy
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hy
    have hvalid : pair c (FiniteWordProjectionRank.word D c k) ∈ allowed F cone height := (Finset.mem_filter.mp hk).2
    let w := FiniteWordProjectionRank.word D c k
    have hw := allowed_good F cone height c w hvalid
    let v : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ := (SquareSampleCompleteVertices.candidate I s w hw).val
    have hvroot := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs v).mp
      (SquareSampleCompleteVertices.candidate I s w hw).property
    have HV := FlatAffineEndpointFiniteProjection.equations F height s v hvroot
    have hh := allowed_heights F cone height c w ha hvalid
    refine ⟨FlatAffineEndpointFiniteProjection.copy F s v 0, ?_, ?_⟩
    · intro i
      have hi := HV.2.2 (0 : Fin 3) i
      have ht : FlatAffineEndpointFiniteProjection.sample F s z = FlatAffineEndpointFiniteProjection.sample F s v := hh.1
      rw [← ht] at hi
      simpa using hi
    · exact he.symm.trans (value_packet F cone height index c w hw)
  · rintro ⟨current, hc, rfl⟩
    obtain ⟨w, hw, _, he⟩ := FlatAffineEndpointFiniteSample.tuple_label_exists F cone height s hs
      (FlatAffineEndpointFiniteProjection.endpoint F s z) (FlatAffineEndpointFiniteProjection.sample F s z) current
      (FlatAffineEndpointFiniteProjection.copy F s z 1) (FlatAffineEndpointFiniteProjection.copy F s z 2) H.2.1 H.1 hc
      (by intro i; simpa using H.2.2 (1 : Fin 3) i) (by intro i; simpa using H.2.2 (2 : Fin 3) i)
    let v : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ := (SquareSampleCompleteVertices.candidate I s w hw).val
    have hp : ∀ i, i.val < 2 → z i = v i := by
      apply (height_prefix_iff F s z v).mpr
      constructor
      · exact ((congrArg (FlatAffineEndpointFiniteProjection.sample F s) he).trans
          (FlatAffineEndpointFiniteProjection.sample_point F s _ _ current _ _)).symm
      · exact ((congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
          (FlatAffineEndpointFiniteProjection.endpoint_point F s _ _ current _ _)).symm
    have hallowed : pair c w ∈ allowed F cone height := by
      apply (allowed_packet F cone height c w).mpr
      refine ⟨hs, ?_⟩
      exact (SquareSampleCompletePrefixEquality.packet I (FlatAffineEndpointFiniteSample.complete F cone height)
        (fun _ => 2) s (anchor c) w ha hw (by
          change 2 ≤ FlatAffineEndpointFiniteFrame.arity F s
          dsimp only [FlatAffineEndpointFiniteFrame.arity, FlatAffineEndpointRows.arity]
          omega)).mpr hp
    have hlen : w.length = D.width c := (Classical.choose hw).1
    let k := Nat.fromBitsLE w
    have hk : k < 2 ^ D.width c := by simpa only [hlen] using Nat.fromBitsLE_lt_pow_length w
    have hword : FiniteWordProjectionRank.word D c k = w := by
      change ImplicitGraph.word (D.width c) (Nat.fromBitsLE w) = w
      rw [← hlen, ImplicitGraph.word_fromBitsLE]
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩, ?_⟩
    · rw [hword]
      exact hallowed
    · change D.value c (FiniteWordProjectionRank.word D c k) = current (index c)
      rw [hword, value_packet F cone height index c w hw]
      have hv : FlatAffineEndpointFiniteProjection.copy F s v 0 = current := by
        have hh := (congrArg (fun v => FlatAffineEndpointFiniteProjection.copy F s v 0) he).trans
          (FlatAffineEndpointFiniteProjection.copy_point F s _ _ current _ _ 0)
        exact hh
      exact congrFun hv (index c)

end LeanCanny.Encoding.FlatAffineEndpointFiniteRanks
