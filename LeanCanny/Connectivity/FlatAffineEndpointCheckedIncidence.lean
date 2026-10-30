/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteEdges
public import LeanCanny.Connectivity.FlatAffineEndpointFiniteIncidence
public import LeanCanny.Connectivity.FlatAffineEndpointCellIncidence

/-! # Native endpoint incidence with checked adjacent sample labels

The query compares its scalar height labels with the joint root, checks
exact adjacency, and decides all-candidate matching. Its answer is actual
left or right slab attachment. No retained-gap membership is supplied
as an unchecked premise.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointCheckedIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w aWord tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
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
    (hq : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height true)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteEdges.language F cone height true ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b (.inl j) (.inr (.inl x)) := by
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have heA : FlatAffineEndpointFiniteProjection.endpoint F s z =
      root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i :=
    (congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
      (FlatAffineEndpointFiniteProjection.endpoint_point F s _ t (curve j t) x.val y)
  have heT : FlatAffineEndpointFiniteProjection.sample F s z = t :=
    (congrArg (FlatAffineEndpointFiniteProjection.sample F s) he).trans
      (FlatAffineEndpointFiniteProjection.sample_point F s _ t (curve j t) x.val y)
  have hgap := FlatAffineEndpointFiniteAdjacent.gap F cone height true s w aWord tWord hs hw haWord htWord i heA.symm hq
  change FlatAffineEndpointFiniteProjection.sample F s z ∈ gap
    (FlatAffineEndpointCells.roots F cone height (pairFst s))
    (if true then rightGap _ i else leftGap _ i) at hgap
  rw [heT] at hgap
  exact (FlatAffineEndpointFiniteEdges.packet F cone height true s w aWord tWord hq).trans
    (FlatAffineEndpointFiniteIncidence.left_iff F cone height s w hs hw i ha curve hc hroot j x t hgap htb y he)

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w aWord tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
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
    (hq : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height false)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteEdges.language F cone height false ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve a
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) (.inl j) (.inr (.inr x)) := by
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have heA : FlatAffineEndpointFiniteProjection.endpoint F s z =
      root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i :=
    (congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
      (FlatAffineEndpointFiniteProjection.endpoint_point F s _ t (curve j t) x.val y)
  have heT : FlatAffineEndpointFiniteProjection.sample F s z = t :=
    (congrArg (FlatAffineEndpointFiniteProjection.sample F s) he).trans
      (FlatAffineEndpointFiniteProjection.sample_point F s _ t (curve j t) x.val y)
  have hgap := FlatAffineEndpointFiniteAdjacent.gap F cone height false s w aWord tWord hs hw haWord htWord i heA.symm hq
  change FlatAffineEndpointFiniteProjection.sample F s z ∈ gap
    (FlatAffineEndpointCells.roots F cone height (pairFst s))
    (if false then rightGap _ i else leftGap _ i) at hgap
  rw [heT] at hgap
  exact (FlatAffineEndpointFiniteEdges.packet F cone height false s w aWord tWord hq).trans
    (FlatAffineEndpointFiniteIncidence.right_iff F cone height s w hs hw i hb curve hc hroot j x t hgap hat y he)

end LeanCanny.Connectivity.FlatAffineEndpointCheckedIncidence
