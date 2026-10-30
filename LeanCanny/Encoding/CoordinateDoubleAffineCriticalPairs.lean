/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleDoubleProjection
public import LeanCanny.Encoding.CoordinateDoubleAffineChildHeightSamples

/-! # Native pairs of actual original critical samples

Pairing the original next-stage sampler reuses its own cone-derived
completeness proof. Every pair of critical roots has a native paired label,
and each member can be recovered in the original critical sampler context.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords (criticalInput)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem critical_complete (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleComplete.Complete (criticalInput P depth old level) :=
  FlatAffinePowerSampleInput.complete
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level)

theorem critical_access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (criticalInput P depth old level).Access :=
  FlatAffinePowerSampleInput.access
    (FlatAffineCompleteRootStages.access (CoordinateDoubleAffinePrefix.access hP hd ho hl hA) (hd.add (UnaryFn.const 1)))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level)

noncomputable def input (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  SquareSampleDouble.input (criticalInput P depth old level) (critical_complete P depth old level)

theorem complete (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleComplete.Complete (input P depth old level) :=
  SquareSampleDouble.complete (criticalInput P depth old level) (critical_complete P depth old level)

theorem access {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (input P depth old level).Access :=
  SquareSampleDouble.access (critical_access hP hd ho hl hA) (critical_complete P depth old level)

noncomputable def memberWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) : List Bool → List Bool :=
  SquareSampleDouble.value (criticalInput P depth old level) (critical_complete P depth old level) right

theorem memberWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) (right : Bool) :
    SpaceFunction (memberWord P depth old level right) :=
  SquareSampleDouble.evaluator (critical_access hP hd ho hl hA) (critical_complete P depth old level) right

theorem memberWord_valid (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    SquareSampleCompleteVertices.Valid (criticalInput P depth old level) u (memberWord P depth old level right (LeanCanny.pair u w)) :=
  SquareSampleDouble.value_valid (criticalInput P depth old level) (critical_complete P depth old level) right u w hw

theorem memberWord_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    (SquareSampleCompleteVertices.candidate (criticalInput P depth old level) u
      (memberWord P depth old level right (LeanCanny.pair u w)) (memberWord_valid P depth old level right u w hw)).val =
      (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val ∘
        SquareSampleDouble.projection (criticalInput P depth old level) right u :=
  SquareSampleDouble.value_point (criticalInput P depth old level) (critical_complete P depth old level) right u w hw

theorem exists_pair (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x y : SquareSampleComplete.Roots (criticalInput P depth old level) u) :
    ∃ (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w),
      (∀ right : Bool, SquareSampleCompleteVertices.candidate (criticalInput P depth old level) u
        (memberWord P depth old level right (LeanCanny.pair u w)) (memberWord_valid P depth old level right u w hw) =
          if right then y else x) := by
  let w := SquareSampleDouble.wordPair (criticalInput P depth old level) (critical_complete P depth old level) u x y
  have hw := SquareSampleDouble.wordPair_valid (criticalInput P depth old level) (critical_complete P depth old level) u x y
  exact ⟨w, hw, fun right => SquareSampleDouble.value_wordPair (criticalInput P depth old level)
    (critical_complete P depth old level) u right x y⟩

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
