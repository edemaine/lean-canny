/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSweep
public import LeanCanny.Encoding.FlatAffineLevelRecordData
public import LeanCanny.Encoding.FlatAffineSlicePresentation

/-! # The actual coordinate sweep has the original slice as its coarser domain

Changing the active prefix leaves the stored affine level values unchanged.
The retained parent has the same original coordinates. Removing the newly
active sweep height therefore recovers exactly the original spatial slice.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSweep
open Set LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

theorem levels_eq (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs P depth old level) u k j =
      FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j := by
  calc
    _ = FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k
        (FlatAffineLevelRecordData.data (CoordinateAffinePrefix.levels P (objective depth old) level
          (FlatAffineFullSourceTower.levelQuery u k j.val))) :=
      FlatAffineLevelRecordData.level_eq_data (inputs P depth old level) u k j
    _ = FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k
        (FlatAffineLevelRecordData.data (CoordinateAffinePrefix.levels P old level
          (FlatAffineFullSourceTower.levelQuery u k j.val))) :=
      congrArg (FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k)
        (FlatAffineLevelRecordData.prefix_data P (objective depth old) old level _)
    _ = _ := (FlatAffineLevelRecordData.level_eq_data
      (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j).symm

noncomputable def parent (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) u) :
    FlatAffinePowerSampleInput.OriginalRoots (inputs P depth old level) u :=
  FlatAffineSlicePresentation.rootOfSystemEq
    (FlatAffineFullSourceTower.system (CoordinateDoubleAffinePrefix.inputs P depth old level) u)
    (FlatAffineFullSourceTower.system (inputs P depth old level) u)
    (parent_system P depth old level u).symm x

theorem parent_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) u) :
    (parent P depth old level u x).val = x.val :=
  FlatAffineSlicePresentation.rootOfSystemEq_val _ _ (parent_system P depth old level u).symm x

attribute [local irreducible] parent

theorem normal_eq (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j i : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.direction (inputs P depth old level) u k j.succ i =
      FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j.succ i :=
  (CoordinateDoubleAffinePrefix.normal P depth (objective depth old) level u k j i).trans
    (CoordinateDoubleAffinePrefix.normal P depth old level u k j i).symm

theorem coarse_slice (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (hn : old (FlatAffineFullSourceTower.stage u (depth u)) < P.dim u + 3)
    (x : FlatAffinePowerSampleInput.OriginalRoots (CoordinateDoubleAffinePrefix.inputs P depth old level) u) :
    FlatAffineShiftedSlice.coarseSlice (inputs P depth old level) u (parent P depth old level u x)
        (CoordinateAffineTower.selected P old u (depth u)) =
      FlatAffineCompleteComponentSamples.slice (CoordinateDoubleAffinePrefix.inputs P depth old level) u x := by
  let n := P.dim u + 4
  have HA := coarse_active P depth old level u hn
  have HD := funext (fun j : Fin n => funext (normal_eq P depth old level u (depth u) j))
  let oldValues (j : Fin n) : ℝ :=
    (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
      (Int.castRingHom ℝ) (x.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (depth u))
  let newValues (j : Fin n) : ℝ :=
    (FlatAffineFullSourceTower.level (inputs P depth old level) u (depth u) j).polynomial.eval₂
      (Int.castRingHom ℝ) ((parent P depth old level u x).val ∘
        TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (depth u))
  have HB : newValues = oldValues := by
    funext j
    have HL := congrArg (fun b : FlatAffineCriticalTower.Level n (depth u) ℤ =>
      b.polynomial.eval₂ (Int.castRingHom ℝ) ((parent P depth old level u x).val ∘
        TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (depth u)))
      (levels_eq P depth old level u (depth u) j)
    have HX := congrArg (fun z : Fin (FlatAffineFullSourceTower.count (CoordinateDoubleAffinePrefix.inputs P depth old level) u) → ℝ =>
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j).polynomial.eval₂
        (Int.castRingHom ℝ) (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width n) (depth u)))
      (parent_val P depth old level u x)
    exact HL.trans HX
  have HH := FlatAffineSlicePresentation.set_congr (BoundedFullCriticalSamples.polynomial P u) HA HD HB
  exact (FlatAffineSlicePresentation.coarse (inputs P depth old level) u (parent P depth old level u x) _).trans
    (HH.trans (FlatAffineSlicePresentation.original (CoordinateDoubleAffinePrefix.inputs P depth old level) u x).symm)


end LeanCanny.Encoding.CoordinateDoubleAffineSweep
