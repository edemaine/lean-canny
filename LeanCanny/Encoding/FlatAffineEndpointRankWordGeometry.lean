/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWord
public import LeanCanny.Encoding.FlatAffineEndpointFiniteRankBranch

/-! # The assembled native descriptor denotes the actual branch-rank vector

Source-indexed scalar wrappers preserve packet normalization before dependent
coordinate objects are opened. The geometric branch family is used only in
correctness proofs; it supplies no runtime reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRankWord
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def anchorPoint (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
  if hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w then
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val else 0

theorem anchorPoint_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w) :
    anchorPoint F cone height s w =
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val := dite_eq_left hw

noncomputable def sampleValue (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool) : ℝ :=
  FlatAffineEndpointFiniteProjection.sample F s (anchorPoint F cone height s w)

noncomputable def currentValue (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool) : Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ :=
  FlatAffineEndpointFiniteProjection.copy F s (anchorPoint F cone height s w) 0

noncomputable def BranchView {J : Type*} (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) : Prop :=
  (∀ k, points s (sampleValue F cone height s w) k ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s (sampleValue F cone height s w)) ∧
    (∀ current, current ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s (sampleValue F cone height s w) →
      ∃ k, points s (sampleValue F cone height s w) k = current) ∧
    currentValue F cone height s w = points s (sampleValue F cone height s w) j

noncomputable def branchOrdinal {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w iWord : List Bool) : ℕ :=
  AlgebraicFiberImageRank.rank (points s (sampleValue F cone height s w)) j (FlatAffineEndpointFiniteSide.coordinate F s iWord)

noncomputable def branchWord {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) : List Bool :=
  FixedWidthNatVector.encode (FlatAffineEndpointFiniteSide.originalCount F s)
    (SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) s + 1)
    (fun i => branchOrdinal F cone height points j s w (BinaryNatCode.encode i))

theorem ordinal_packet {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (b : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height (pairFst b))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst b) (pairSnd b))
    (hv : BranchView F cone height points j (pairFst b) (pairSnd b)) (i : ℕ) :
    ordinal F cone height b i = branchOrdinal F cone height points j (pairFst b) (pairSnd b) (BinaryNatCode.encode i) := by
  let c := rankContext (pair b (BinaryNatCode.encode i))
  have hf : FlatAffineEndpointFiniteRanks.frame c = pairFst b := by
    simp only [c, rankContext, FlatAffineEndpointFiniteRanks.frame, pairFst_pair]
  have ha : FlatAffineEndpointFiniteRanks.anchor c = pairSnd b := by
    simp only [c, rankContext, FlatAffineEndpointFiniteRanks.anchor, pairFst_pair, pairSnd_pair]
  have hi : pairSnd (pairSnd c) = BinaryNatCode.encode i := by simp only [c, rankContext, pairSnd_pair]
  have hs' : FlatAffineEndpointFiniteFrame.Valid F height (FlatAffineEndpointFiniteRanks.frame c) := by rw [hf]; exact hs
  have hw' : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) := by rw [hf, ha]; exact hw
  have hv' : BranchView F cone height points j (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) := by
    rw [hf, ha]
    exact hv
  have hp := anchorPoint_packet F cone height _ _ hw'
  have ht : sampleValue F cone height (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) =
      FlatAffineEndpointFiniteProjection.sample F (FlatAffineEndpointFiniteRanks.frame c)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
          (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) hw').val :=
    congrArg (FlatAffineEndpointFiniteProjection.sample F (FlatAffineEndpointFiniteRanks.frame c)) hp
  have hc : currentValue F cone height (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) =
      FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointFiniteRanks.frame c)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
          (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c) hw').val 0 :=
    congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointFiniteRanks.frame c) z 0) hp
  have H := FlatAffineEndpointFiniteRanks.branch_packet F cone height (index F) c hs' hw'
    (points (FlatAffineEndpointFiniteRanks.frame c)
      (sampleValue F cone height (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c)))
    (fun k => by change _ ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height _ _; rw [← ht]; exact hv'.1 k)
    (fun current hcurrent => hv'.2.1 current (by
      rw [ht]
      exact hcurrent)) j (hc.symm.trans hv'.2.2)
  have hq : rankQuery (pair b (BinaryNatCode.encode i)) = pair c (FlatAffineEndpointFiniteRanks.anchor c) := by
    simp only [rankQuery, pairFst_pair, c, rankContext, FlatAffineEndpointFiniteRanks.anchor, pairSnd_pair]
  calc
    ordinal F cone height b i = FiniteWordProjectionRank.rank (FlatAffineEndpointFiniteRanks.data F cone height (index F))
        (pair c (FlatAffineEndpointFiniteRanks.anchor c)) :=
      congrArg (FiniteWordProjectionRank.rank (FlatAffineEndpointFiniteRanks.data F cone height (index F))) hq
    _ = branchOrdinal F cone height points j (FlatAffineEndpointFiniteRanks.frame c) (FlatAffineEndpointFiniteRanks.anchor c)
        (pairSnd (pairSnd c)) := H
    _ = _ := by rw [hf, ha, hi]

theorem word_packet {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (b : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height (pairFst b))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst b) (pairSnd b))
    (hv : BranchView F cone height points j (pairFst b) (pairSnd b)) :
    word F cone height b = branchWord F cone height points j (pairFst b) (pairSnd b) := by
  unfold word branchWord
  apply congrArg (FixedWidthNatVector.encode (arity F b) (width F cone height b))
  funext i
  exact ordinal_packet F cone height points j b hs hw hv i

theorem ordinal_packet_pair {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : BranchView F cone height points j s w) (i : ℕ) :
    ordinal F cone height (pair s w) i = branchOrdinal F cone height points j s w (BinaryNatCode.encode i) := by
  have H := ordinal_packet F cone height points j (pair s w)
    (by simpa only [pairFst_pair] using hs) (by simpa only [pairFst_pair, pairSnd_pair] using hw)
    (by simpa only [pairFst_pair, pairSnd_pair] using hv) i
  simpa only [pairFst_pair, pairSnd_pair] using H

theorem word_packet_pair {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : BranchView F cone height points j s w) :
    word F cone height (pair s w) = branchWord F cone height points j s w := by
  have H := word_packet F cone height points j (pair s w)
    (by simpa only [pairFst_pair] using hs) (by simpa only [pairFst_pair, pairSnd_pair] using hw)
    (by simpa only [pairFst_pair, pairSnd_pair] using hv)
  simpa only [pairFst_pair, pairSnd_pair] using H

theorem branchOrdinal_bits {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : BranchView F cone height points j s w) (i : ℕ) :
    (branchOrdinal F cone height points j s w (BinaryNatCode.encode i)).size ≤
      SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) s + 1 := by
  have H := ordinal_bits F cone height (pair s w) i
  rw [ordinal_packet_pair F cone height points j s w hs hw hv i] at H
  simpa only [width, pairFst_pair] using H

theorem branchWord_decode {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : BranchView F cone height points j s w) (i : ℕ) (hi : i < FlatAffineEndpointFiniteSide.originalCount F s) :
    let W := SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) s + 1
    Nat.fromBitsLE (((branchWord F cone height points j s w).drop (i * W)).take W) =
      branchOrdinal F cone height points j s w (BinaryNatCode.encode i) :=
  FixedWidthNatVector.decode_block _ _ _ i hi (Nat.size_le.mp (branchOrdinal_bits F cone height points j s w hs hw hv i))

end LeanCanny.Encoding.FlatAffineEndpointRankWord
