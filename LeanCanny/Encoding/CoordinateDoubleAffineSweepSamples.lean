/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSweep
public import LeanCanny.Encoding.SquareSampleProjectionChoice

/-! # Native frozen-parent label conversion into the next coordinate sweep

Advancing the newest objective leaves every equation in the retained parent
power system unchanged. Native projected-label search re-encodes a parent
word in the sweep sampler and preserves every coordinate of its power root.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSweep
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleProjectionChoice.language
  SquareSampleCompleteVertices.Valid

theorem parent_power_system (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffinePowerPositive.system (inputs P depth old level) u =
      FlatAffinePowerPositive.system (CoordinateDoubleAffinePrefix.inputs P depth old level) u := by
  have HS := funext (fun t : Fin (depth u) => free_before P depth old level u t.val t.isLt)
  have HD := funext (fun t : Fin (depth u) => direction_before P depth old level u t.val t.isLt)
  have HL := funext (fun t : Fin (depth u) => funext (level_before P depth old level u t.val t.isLt))
  let build (s : Fin (depth u) → Finset (Fin (P.dim u + 4)))
      (a : Fin (depth u) → Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : (t : Fin (depth u)) → Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) t.val ℤ) :=
    PositivePolynomialSystem.system (FlatAffinePowerTower.system
      (BoundedFullCriticalSamples.polynomial P u) (FlatAffinePowerControls.degree (inputs P depth old level) u) s a b)
  change build (fun t => FlatAffineFullSourceTower.free (inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (inputs P depth old level) u t.val) =
    build (fun t => FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
      (fun t => FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u t.val)
  rw [HS, HD, HL]

noncomputable def parentInput (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (CoordinateDoubleAffinePrefix.inputs P depth old level)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth old level)

noncomputable def sweepInput (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (inputs P depth old level)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth (objective depth old) level)

noncomputable def parentWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (parentInput P depth old level) (sweepInput P depth old level) (fun _ i => i)

theorem parentWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceFunction (parentWord P depth old level) := by
  have A := FlatAffinePowerSampleInput.access (CoordinateDoubleAffinePrefix.access hP hd ho hl hA)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth old level)
  have B := FlatAffinePowerSampleInput.access (access hP hd ho hl hA)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth (objective depth old) level)
  exact SquareSampleProjectionChoice.evaluator A B (fun _ i => i) (SquareSampleCompleteCoordinateThom.coordinate_unary B)

theorem parentWord_projects (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (x : SquareSampleComplete.Roots (parentInput P depth old level) u) :
    ∀ i, ((sweepInput P depth old level).system u i).eval₂ (Int.castRingHom ℝ) (x.val ∘ (fun i => i)) = 0 := by
  intro i
  change (FlatAffinePowerPositive.system (inputs P depth old level) u i).eval₂ (Int.castRingHom ℝ) x.val = 0
  rw [parent_power_system P depth old level u]
  exact x.property i

theorem parentWord_valid (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (parentInput P depth old level) u w) :
    SquareSampleCompleteVertices.Valid (sweepInput P depth old level) u (parentWord P depth old level (pair u w)) :=
  SquareSampleProjectionChoice.value_valid (parentInput P depth old level) (sweepInput P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs P depth old level) _)
    (fun _ i => i) (parentWord_projects P depth old level) u w hw

theorem parentWord_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (parentInput P depth old level) u w) :
    (SquareSampleCompleteVertices.candidate (sweepInput P depth old level) u (parentWord P depth old level (pair u w))
      (parentWord_valid P depth old level u w hw)).val =
      (SquareSampleCompleteVertices.candidate (parentInput P depth old level) u w hw).val :=
  SquareSampleProjectionChoice.value_point (parentInput P depth old level) (sweepInput P depth old level)
    (FlatAffinePowerSampleInput.complete (inputs P depth old level) _)
    (fun _ i => i) (parentWord_projects P depth old level) u w hw

end LeanCanny.Encoding.CoordinateDoubleAffineSweep
