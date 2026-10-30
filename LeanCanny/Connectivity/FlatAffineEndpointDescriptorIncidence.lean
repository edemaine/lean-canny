/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointDescriptorMatching
public import LeanCanny.Connectivity.FlatAffineEndpointCheckedIncidence

/-! # Complete native attachment queries decide actual descriptor-to-point edges

The existential native query is equivalent to the actual left or right slab
edge from the reference branch to the independently labeled endpoint marker.
All witness tuples are eliminated by exact descriptor and point identities.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointDescriptorIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open FlatAffineEndpointRankWord (sampleValue BranchView word)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem left_iff {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s r v aWord tWord gapWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hr : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s r)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (haWord : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (htWord : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (hView : BranchView F cone height points j s r)
    (hSlab : pair (pair s r) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (hAdj : pair (pair s r) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height true)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card) {b : ℝ}
    (hi : (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord haWord).val (0 : Fin 1) =
      root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
    (ha : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (hc : ∀ k, ContinuousOn (fun t => points s t k) (Icc (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b))
    (hroot : ∀ k t, t ∈ Icc (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b →
      equation F height (pairFst s) t (points s t k))
    (htb : sampleValue F cone height s r < b)
    (x : FiniteFiberSlab.Fiber (equation F height (pairFst s)) (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i))
    (hx : FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1 = x.val) :
    FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
        FlatAffineEndpointIncidenceQuery.language F cone height true ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) (fun k t => points s t k)
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b (.inl j) (.inr (.inl x)) := by
  let a : ℝ := (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord haWord).val (0 : Fin 1)
  let marker := FlatAffineEndpointFiniteProjection.copy F s
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1
  let current := FlatAffineEndpointFiniteProjection.copy F s
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val 0
  have HM : FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
      FlatAffineEndpointIncidenceQuery.language F cone height true ↔
      EndpointMidpoint.Matches (FlatAffineEndpointFiniteMatching.endpointFiber F height s a) marker current :=
    ⟨FlatAffineEndpointDescriptorMatching.sound F cone height points j s r v aWord tWord gapWord hs hr hv haWord hView hSlab hMarker true,
      FlatAffineEndpointDescriptorMatching.complete F cone height points j s r v aWord tWord gapWord hs hr hv haWord hView hSlab hMarker true hAdj⟩
  have AP := (FlatAffineEndpointFiniteAdjacent.packet F cone height true s r aWord tWord hs hr haWord htWord).mp hAdj
  have HA : root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i = FlatAffineEndpointFiniteProjection.endpoint F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val :=
    (AP.1.trans hi).symm
  have HG := FlatAffineEndpointFiniteAdjacent.gap F cone height true s r aWord tWord hs hr haWord htWord i HA hAdj
  have HT : sampleValue F cone height s r = FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val :=
    congrArg (FlatAffineEndpointFiniteProjection.sample F s) (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s r hr)
  have hgap : sampleValue F cone height s r ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (rightGap _ i) :=
    (congrArg (fun t => t ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (rightGap _ i)) HT).mpr HG
  have HC : current = points s (sampleValue F cone height s r) j :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s r hr)).symm.trans hView.2.2
  have MM : EndpointMidpoint.Matches (FlatAffineEndpointFiniteMatching.endpointFiber F height s a) marker current ↔
      EndpointMidpoint.Matches {y | equation F height (pairFst s) (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) y}
        x.val (points s (sampleValue F cone height s r) j) := by
    rw [show a = root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i from hi, show marker = x.val from hx, HC]
    rfl
  exact HM.trans (MM.trans (FlatAffineEndpointCellIncidence.left_iff F cone height (pairFst s) hs.1 i ha
    (fun k t => points s t k) hc hroot j x (sampleValue F cone height s r) hgap htb))

theorem right_iff {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s r v aWord tWord gapWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hr : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s r)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (haWord : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (htWord : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (hView : BranchView F cone height points j s r)
    (hSlab : pair (pair s r) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (hAdj : pair (pair s r) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height false)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card) {aBound : ℝ}
    (hi : (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord haWord).val (0 : Fin 1) =
      root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
    (ha : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (hc : ∀ k, ContinuousOn (fun t => points s t k) (Icc aBound (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)))
    (hroot : ∀ k t, t ∈ Icc aBound (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) →
      equation F height (pairFst s) t (points s t k))
    (hat : aBound < sampleValue F cone height s r)
    (x : FiniteFiberSlab.Fiber (equation F height (pairFst s)) (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i))
    (hx : FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1 = x.val) :
    FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
        FlatAffineEndpointIncidenceQuery.language F cone height false ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) (fun k t => points s t k)
        aBound (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) (.inl j) (.inr (.inr x)) := by
  let a : ℝ := (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord haWord).val (0 : Fin 1)
  let marker := FlatAffineEndpointFiniteProjection.copy F s
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1
  let current := FlatAffineEndpointFiniteProjection.copy F s
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val 0
  have HM : FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
      FlatAffineEndpointIncidenceQuery.language F cone height false ↔
      EndpointMidpoint.Matches (FlatAffineEndpointFiniteMatching.endpointFiber F height s a) marker current :=
    ⟨FlatAffineEndpointDescriptorMatching.sound F cone height points j s r v aWord tWord gapWord hs hr hv haWord hView hSlab hMarker false,
      FlatAffineEndpointDescriptorMatching.complete F cone height points j s r v aWord tWord gapWord hs hr hv haWord hView hSlab hMarker false hAdj⟩
  have AP := (FlatAffineEndpointFiniteAdjacent.packet F cone height false s r aWord tWord hs hr haWord htWord).mp hAdj
  have HA : root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i = FlatAffineEndpointFiniteProjection.endpoint F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val :=
    (AP.1.trans hi).symm
  have HG := FlatAffineEndpointFiniteAdjacent.gap F cone height false s r aWord tWord hs hr haWord htWord i HA hAdj
  have HT : sampleValue F cone height s r = FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val :=
    congrArg (FlatAffineEndpointFiniteProjection.sample F s) (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s r hr)
  have hgap : sampleValue F cone height s r ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (leftGap _ i) :=
    (congrArg (fun t => t ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (leftGap _ i)) HT).mpr HG
  have HC : current = points s (sampleValue F cone height s r) j :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s r hr)).symm.trans hView.2.2
  have MM : EndpointMidpoint.Matches (FlatAffineEndpointFiniteMatching.endpointFiber F height s a) marker current ↔
      EndpointMidpoint.Matches {y | equation F height (pairFst s) (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) y}
        x.val (points s (sampleValue F cone height s r) j) := by
    rw [show a = root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i from hi, show marker = x.val from hx, HC]
    rfl
  exact HM.trans (MM.trans (FlatAffineEndpointCellIncidence.right_iff F cone height (pairFst s) hs.1 i ha
    (fun k t => points s t k) hc hroot j x (sampleValue F cone height s r) hgap hat))

end LeanCanny.Connectivity.FlatAffineEndpointDescriptorIncidence
