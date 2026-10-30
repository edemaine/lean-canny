/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointIncidenceQuery
public import LeanCanny.Connectivity.FlatAffineEndpointCheckedIncidence

/-! # Native branch-to-marker attachment is actual slab incidence

The auxiliary joint tuple may use a different endpoint label from the graph
marker. Native projected-point equality identifies the actual endpoint point.
After the adjacent height and slab checks, the bounded query test is exactly
geometric attachment together with the requested short branch descriptor.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointMarkerIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w aWord tWord gapWord descriptor v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card) {b : ℝ}
    (ha : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (curve : J → ℝ → Fin (count F (pairFst (pairFst s))) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b))
    (hroot : ∀ j t, t ∈ Icc (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b →
      equation F height (pairFst s) t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height (pairFst s))
      (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i))
    (t : ℝ) (htb : t < b)
    (haWord : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (htWord : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (hAdj : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height true)
    (hSlab : pair (pair s w) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (hx : x.val = FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    FlatAffineEndpointIncidenceQuery.accepts F cone height true
      (pair (FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord descriptor v) w) ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b (.inl j) (.inr (.inl x)) ∧
      FlatAffineEndpointRankWord.word F cone height (pair s w) = descriptor := by
  have hCopy : FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 1 =
      FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1 :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1) he).trans
      ((FlatAffineEndpointFiniteProjection.copy_point F s _ t (curve j t) x.val y 1).trans hx)
  have H := FlatAffineEndpointIncidenceQuery.packet F cone height true s aWord tWord gapWord descriptor v w
    hs hw hv haWord hAdj hSlab hMarker hCopy
  exact H.trans (and_congr
    (FlatAffineEndpointCheckedIncidence.left_iff F cone height s w aWord tWord hs hw i ha curve hc hroot
      j x t htb haWord htWord hAdj y he) Iff.rfl)

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w aWord tWord gapWord descriptor v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card) {a : ℝ}
    (hb : SymbolicScaledSquarefree.scalarEvaluation (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (curve : J → ℝ → Fin (count F (pairFst (pairFst s))) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc a (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)))
    (hroot : ∀ j t, t ∈ Icc a (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) →
      equation F height (pairFst s) t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height (pairFst s))
      (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i))
    (t : ℝ) (hat : a < t)
    (haWord : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (htWord : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (hAdj : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height false)
    (hSlab : pair (pair s w) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (hx : x.val = FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    FlatAffineEndpointIncidenceQuery.accepts F cone height false
      (pair (FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord descriptor v) w) ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve a
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) (.inl j) (.inr (.inr x)) ∧
      FlatAffineEndpointRankWord.word F cone height (pair s w) = descriptor := by
  have hCopy : FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 1 =
      FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1 :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1) he).trans
      ((FlatAffineEndpointFiniteProjection.copy_point F s _ t (curve j t) x.val y 1).trans hx)
  have H := FlatAffineEndpointIncidenceQuery.packet F cone height false s aWord tWord gapWord descriptor v w
    hs hw hv haWord hAdj hSlab hMarker hCopy
  exact H.trans (and_congr
    (FlatAffineEndpointCheckedIncidence.right_iff F cone height s w aWord tWord hs hw i hb curve hc hroot
      j x t hat haWord htWord hAdj y he) Iff.rfl)

end LeanCanny.Connectivity.FlatAffineEndpointMarkerIncidence
