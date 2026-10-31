/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointProjection
public import LeanCanny.Encoding.CoordinateDoubleAffineMidpointPairRoots
public import LeanCanny.Encoding.FlatAffinePowerRootLift

/-! # Shared critical pairs project to actual powered midpoint roots -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra
open CoordinateDoubleAffineChildRecords (childInput inputs criticalInput)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberRoot memberWord midpointRoot SquareSampleCompleteVertices.Valid

theorem memberRoot_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    (memberRoot P depth old level right u w hw).val =
      FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs true P depth old level) u)
        (fun i : Fin (FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u)) =>
          (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val
            (FlatAffinePairedProjection.slot (P.dim u + 4) (depth u) right i.castSucc)) := by
  have HP := memberWord_point P depth old level right u w hw
  have HE := congrArg (fun z : Fin ((criticalInput P depth old level).count u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs true P depth old level) u)
      (z ∘ Fin.castSucc)) HP
  unfold memberRoot
  exact HE

theorem projected_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (inputs true P depth old level) u)
      (((SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val ∘
        midpointProjection P depth old level u) ∘ Fin.castSucc) =
      (midpointRoot P depth old level u w hw hs).val := by
  have HL := (CoordinateDoubleAffineChildRecords.midpointPrefixRoot_val P depth old level u
    (memberRoot P depth old level false u w hw)).trans (memberRoot_point P depth old level false u w hw)
  have HR := congrArg (FlatAffineCompleteRootStages.newest (CoordinateDoubleAffinePrefix.inputs P depth old level) u)
    (memberRoot_point P depth old level true u w hw)
  have HM := CoordinateDoubleAffineChildRecords.midpointRoot_val P depth old level u
    (memberRoot P depth old level false u w hw) (memberRoot P depth old level true u w hw)
    (shared_originals P depth old level u w hw hs)
  unfold midpointRoot
  exact (FlatAffinePairedProjection.powerPoint_projection (P.dim u + 4) (depth u)
    (FlatAffinePowerControls.degree (inputs true P depth old level) u)
    (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val).trans
      ((congrArg₂ (FlatAffineTowerRegularity.appendPoint (depth u + 1)) HL HR).symm.trans HM.symm)

theorem projected_zero (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    ((SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val ∘
      midpointProjection P depth old level u)
        (Fin.last (FlatAffineFullSourceTower.count (inputs true P depth old level) u)) = 0 := by
  have H := (SquareSampleDouble.roots_iff (criticalInput P depth old level) u
    (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val).mp
      (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).property false
  have HZ := ((PositivePolynomialSystem.roots_iff (Int.castRingHom ℝ)
    (FlatAffinePowerPositive.rawSystem
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u) _).mp H).2
  have HE := congrArg (SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val
    (FlatAffinePairedProjection.projection_last (P.dim u + 4) (depth u))
  exact HE.trans HZ

theorem projected_roots_at (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w)
    (hs : LeanCanny.pair u w ∈ sharedLanguage P depth old level) :
    ∀ i, ((childInput true P depth old level).system u i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate (input P depth old level) u w hw).val ∘
        midpointProjection P depth old level u) = 0 :=
  FlatAffinePowerSampleInput.roots_of_original_point (inputs true P depth old level) u _
    (midpointRoot P depth old level u w hw hs) (projected_point P depth old level u w hw hs)
    (projected_zero P depth old level u w hw)

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
