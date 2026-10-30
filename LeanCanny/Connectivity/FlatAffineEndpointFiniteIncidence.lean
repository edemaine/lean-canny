/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteMatching
public import LeanCanny.Connectivity.FlatAffineEndpointCellIncidence

/-! # Native joint matching answers actual slab endpoint-incidence queries

For a complete label denoting a current branch point and endpoint candidate,
the native all-candidate matching language decides the actual left or right
attachment. An accepted adjacent sample supplies the retained-gap condition;
no regularity is imposed on the endpoint root or its joint label.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointFiniteIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
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
    (t : ℝ) (ht : t ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (rightGap _ i)) (htb : t < b)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    pair s w ∈ FlatAffineEndpointFiniteMatching.language F cone height ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) b (.inl j) (.inr (.inl x)) := by
  exact (FlatAffineEndpointFiniteMatching.tuple_packet F cone height s w hs hw _ t _ x.val y he).trans
    (FlatAffineEndpointCellIncidence.left_iff F cone height (pairFst s) hs.1 i ha curve hc hroot j x t ht htb)

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
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
    (t : ℝ) (ht : t ∈ gap (FlatAffineEndpointCells.roots F cone height (pairFst s)) (leftGap _ i)) (hat : a < t)
    (y : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointFiniteLift.point F s (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i)
        t (curve j t) x.val y) :
    pair s w ∈ FlatAffineEndpointFiniteMatching.language F cone height ↔
      FiniteFiberSlab.Edge (equation F height (pairFst s)) curve a
        (root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i) (.inl j) (.inr (.inr x)) := by
  exact (FlatAffineEndpointFiniteMatching.tuple_packet F cone height s w hs hw _ t _ x.val y he).trans
    (FlatAffineEndpointCellIncidence.right_iff F cone height (pairFst s) hs.1 i hb curve hc hroot j x t ht hat)

end LeanCanny.Connectivity.FlatAffineEndpointFiniteIncidence
