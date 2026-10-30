/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointBranchLabels
public import LeanCanny.Encoding.FlatAffineEndpointRankWordSample

/-! # Native branch labels enumerate exactly a complete geometric fiber

Reference tuples are mathematical correctness data. The runtime validator
continues to search the original complete joint labels. No reference table
reader or branch selection oracle is supplied to that computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointBranchLabels
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointRankWord
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] FlatAffineEndpointRankWord.word FlatAffineEndpointSampleSlab.language

theorem language_iff_fiber {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (s tWord gapWord : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (htWord : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (t : ℝ) (ht : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height)
      (pairFst s) tWord htWord).val (0 : Fin 1) = t)
    (hroot : ∀ j, points s t j ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t)
    (hcover : ∀ x, x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t → ∃ j, points s t j = x)
    (refs : J → List Bool)
    (hRef : ∀ j, SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s (refs j))
    (hT : ∀ j, sampleValue F cone height s (refs j) = t)
    (hC : ∀ j, currentValue F cone height s (refs j) = points s t j)
    (hSlab : ∀ j, pair (pair s (refs j)) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (d : List Bool) :
    pair (pair s (pair tWord gapWord)) d ∈ language F cone height ↔
      ∃ j, word F cone height (pair s (refs j)) = d := by
  constructor
  · rintro ⟨w, _, hSW, hWord⟩
    have SW : pair (pair s w) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height := by
      simpa only [slabQuery, candidateQuery, source, samplePacket, pairFst_pair, pairSnd_pair] using hSW
    have HW : word F cone height (pair s w) = d := by
      simpa only [candidateQuery, source, descriptor, pairFst_pair, pairSnd_pair] using hWord
    have hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w := by
      simpa only [pairFst_pair, pairSnd_pair] using FlatAffineEndpointSampleSlab.joint_valid F cone height _ SW
    have SI := SW
    unfold FlatAffineEndpointSampleSlab.language at SI
    have HE := (FlatAffineEndpointFiniteHeights.sample_packet F cone height s w tWord hs hw htWord).mp (by
      simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
        pairFst_pair, pairSnd_pair] using SI.2.1)
    have AT := congrArg (FlatAffineEndpointFiniteProjection.sample F s) (anchorPoint_packet F cone height s w hw)
    have WT : sampleValue F cone height s w = t := AT.trans (HE.trans ht)
    have RX := current_in_fiber F cone height s w hs hw
    rw [WT] at RX
    obtain ⟨j, hj⟩ := hcover _ RX
    have VW := view_at_sample F cone height points j s w t hroot hcover WT hj.symm
    have VR := view_at_sample F cone height points j s (refs j) t hroot hcover (hT j) (hC j)
    have EQ := word_eq_of_same_sample_branch F cone height points j s w (refs j) hs hw (hRef j) VW VR (WT.trans (hT j).symm)
    exact ⟨j, EQ.symm.trans HW⟩
  · rintro ⟨j, hj⟩
    apply witness F cone height (pair (pair s (pair tWord gapWord)) d) (refs j)
    · simpa only [slabQuery, candidateQuery, source, samplePacket, pairFst_pair, pairSnd_pair] using hSlab j
    · simpa only [candidateQuery, source, descriptor, pairFst_pair, pairSnd_pair] using hj

theorem words_injective {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s) (t : ℝ)
    (hroot : ∀ j, points s t j ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t)
    (hcover : ∀ x, x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s t → ∃ j, points s t j = x)
    (refs : J → List Bool)
    (hRef : ∀ j, SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s (refs j))
    (hT : ∀ j, sampleValue F cone height s (refs j) = t)
    (hC : ∀ j, currentValue F cone height s (refs j) = points s t j)
    (hinj : Function.Injective (points s t)) : Function.Injective (fun j => word F cone height (pair s (refs j))) := by
  intro j k he
  have V (i : J) := view_at_sample F cone height points i s (refs i) t hroot hcover (hT i) (hC i)
  have H := word_eq_implies_current_eq F cone height points j k s (refs j) (refs k) hs (hRef j) (hRef k)
    (V j) (V k) ((hT j).trans (hT k).symm) he
  exact hinj ((hC j).symm.trans (H.trans (hC k)))

end LeanCanny.Encoding.FlatAffineEndpointBranchLabels
