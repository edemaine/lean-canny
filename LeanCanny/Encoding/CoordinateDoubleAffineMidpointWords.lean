/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointProjectedRoots
public import LeanCanny.Encoding.SquareSampleProjectionChoiceAt

/-! # Native midpoint child words with their exact original roots

The search uses the original source readers and the explicit coordinate
projection. Its correctness requires only the native shared-parent filter.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords (childInput inputs cone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberRoot midpointRoot SquareSampleCompleteVertices.Valid

noncomputable def midpointWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (input P depth old level) (childInput true P depth old level)
    (midpointProjection P depth old level)

theorem midpointWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceFunction (midpointWord P depth old level) :=
  SquareSampleProjectionChoice.evaluator (access hP hd ho hl hA)
    (FlatAffinePowerSampleInput.access (CoordinateDoubleAffineChildRecords.access true hP hd ho hl hA)
      (cone true P depth old level)) (midpointProjection P depth old level) (midpoint_coordinate_unary hP hd)

attribute [local irreducible] midpointWord

theorem midpointWord_valid (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    SquareSampleCompleteVertices.Valid (childInput true P depth old level) u
      (midpointWord P depth old level (LeanCanny.pair u w)) := by
  unfold midpointWord
  exact SquareSampleProjectionChoice.value_valid_at (input P depth old level) (childInput true P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs true P depth old level) (cone true P depth old level))
    (midpointProjection P depth old level) u w hw (projected_roots_at P depth old level u w hw hs)

theorem midpointWord_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    (SquareSampleCompleteVertices.candidate (childInput true P depth old level) u
      (midpointWord P depth old level (LeanCanny.pair u w)) (midpointWord_valid P depth old level u w hw hs)).val =
        (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val ∘
          midpointProjection P depth old level u := by
  unfold midpointWord
  exact SquareSampleProjectionChoice.value_point_at (input P depth old level) (childInput true P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs true P depth old level) (cone true P depth old level))
    (midpointProjection P depth old level) u w hw (projected_roots_at P depth old level u w hw hs)

theorem midpointWord_root (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    FlatAffineCompleteVertices.vertexEquiv (inputs true P depth old level) (cone true P depth old level) u
      ⟨midpointWord P depth old level (LeanCanny.pair u w), midpointWord_valid P depth old level u w hw hs⟩ =
        midpointRoot P depth old level u w hw hs := by
  have HE := congrArg (fun z : Fin ((childInput true P depth old level).count u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs true P depth old level) u)
      (z ∘ Fin.castSucc)) (midpointWord_point P depth old level u w hw hs)
  apply Subtype.ext
  exact HE.trans (projected_point P depth old level u w hw hs)

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
