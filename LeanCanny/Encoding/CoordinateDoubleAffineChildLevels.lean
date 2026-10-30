/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
public import LeanCanny.Encoding.CoordinateHeightRecordSemantics
public import LeanCanny.Algebra.TriangularPolynomialPrefixCongruence
public import LeanCanny.Encoding.FlatAffineSlicePresentation

/-! # Parent equations and exact levels of recursive coordinate children

The retained prefix has exactly the original parent equations. Copied levels
extend their ancestral references, while the new level is the actual native
height or midpoint record. None of these identities assumes regular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra
open FlatAffineFullSourceTower (stage levelQuery)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

theorem prefix_data (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    FlatAffineLevelRecordData.data (CoordinateAffinePrefix.levels P objective level q) =
      FlatAffineLevelRecordData.data (level q) := by
  simp only [FlatAffineLevelRecordData.data, CoordinateAffinePrefix.levels, CoordinateAffinePrefix.setFlags,
    FlatAffineFullSourceTower.tag, FlatAffineFullSourceTower.flags, FlatAffineFullSourceTower.left,
    FlatAffineFullSourceTower.right, FlatAffineFullSourceTower.normal, FlatAffineFullSourceTower.constant,
    pairFst_pair, pairSnd_pair, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

theorem level_raw (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth objective level) u k j =
      FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k (FlatAffineLevelRecordData.data (level (levelQuery u k j.val))) :=
  (FlatAffineLevelRecordData.level_eq_data (CoordinateDoubleAffinePrefix.inputs P depth objective level) u k j).trans
    (congrArg (FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k) (prefix_data P objective level _))

theorem level_record_before (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k j : ℕ) (hk : k < depth u) :
    (inputs midpoint P depth old level).level (levelQuery u k j) =
      (CoordinateDoubleAffinePrefix.inputs P depth old level).level (levelQuery u k j) := by
  change CoordinateAffinePrefix.levels P (objective midpoint depth old) (levels midpoint P depth old level)
      (levelQuery u k j) = CoordinateAffinePrefix.levels P old level (levelQuery u k j)
  unfold CoordinateAffinePrefix.levels
  rw [levels_before midpoint P depth old level u k j hk]
  unfold CoordinateAffinePrefix.setFlags CoordinateAffinePrefix.cut
  simp only [levelQuery, pairFst_pair, pairSnd_pair, objective_before midpoint depth old u k hk]

theorem direction_before (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    FlatAffineFullSourceTower.direction (inputs midpoint P depth old level) u k =
      FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
  funext r i
  change FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u k)) + 4)
        (min (objective midpoint depth old (stage u k)) (P.dim (pairFst (stage u k)) + 3)))
      (r.val * (P.dim u + 4) + i.val) =
    FlatAffineFullSourceTower.integer 2
      (CoordinateDoubleAffineRecord.record (P.dim (pairFst (stage u k)) + 4)
        (min (old (stage u k)) (P.dim (pairFst (stage u k)) + 3)))
      (r.val * (P.dim u + 4) + i.val)
  rw [objective_before midpoint depth old u k hk]

theorem level_before (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u)
    (j : Fin (P.dim u + 4)) :
    FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u k j =
      FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k j := by
  exact congrArg (fun r => FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k (FlatAffineLevelRecordData.data r))
    (level_record_before midpoint P depth old level u k j.val hk)

theorem family_row_before (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : k < depth u) :
    (FlatAffineFullSourceTower.family (inputs midpoint P depth old level) u).row k =
      (FlatAffineFullSourceTower.family (CoordinateDoubleAffinePrefix.inputs P depth old level) u).row k := by
  have HF : FlatAffineFullSourceTower.free (inputs midpoint P depth old level) u k =
      FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u k := by
    unfold FlatAffineFullSourceTower.free
    apply Finset.filter_congr
    intro j _
    rw [level_record_before midpoint P depth old level u k j.val hk]
  have HD := direction_before midpoint P depth old level u k hk
  have HL := funext (level_before midpoint P depth old level u k hk)
  let build (s : Finset (Fin (P.dim u + 4))) (a : Fin (P.dim u + 4 + 1) → Fin (P.dim u + 4) → ℤ)
      (b : Fin (P.dim u + 4) → FlatAffineCriticalTower.Level (P.dim u + 4) k ℤ) :=
    fun i : Fin (FlatAffineCriticalTower.width (P.dim u + 4)) =>
      MvPolynomial.rename
        (Equiv.sumCongr (Equiv.refl (FlatAffineCriticalTower.Ancestors (P.dim u + 4) k))
          (FlatAffineCriticalTower.blockEquiv (P.dim u + 4)))
        (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial P u) s a
          (fun j => (b j).polynomial) ((FlatAffineCriticalTower.blockEquiv (P.dim u + 4)).symm i))
  change build (FlatAffineFullSourceTower.free (inputs midpoint P depth old level) u k)
      (FlatAffineFullSourceTower.direction (inputs midpoint P depth old level) u k)
      (FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u k) =
    build (FlatAffineFullSourceTower.free (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
      (FlatAffineFullSourceTower.direction (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
      (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u k)
  rw [HF, HD, HL]

theorem parent_system (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    FlatAffineFullSourceTower.system (FlatAffineCompleteRootStages.truncate (inputs midpoint P depth old level) depth) u =
      FlatAffineFullSourceTower.system (CoordinateDoubleAffinePrefix.inputs P depth old level) u :=
  TriangularPolynomialIndexing.system_congr _ _ (depth u) (family_row_before midpoint P depth old level u)

theorem level_copy (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ) (hk : depth u ≤ k)
    (j : Fin (P.dim u + 4)) (hj : k ≠ childDepth midpoint depth u ∨ j.val ≠ coordinate P depth old u) :
    FlatAffineFullSourceTower.level (inputs midpoint P depth old level) u k j =
      FlatAffineCriticalTower.Level.extend hk
        (FlatAffineFullSourceTower.level (CoordinateDoubleAffinePrefix.inputs P depth old level) u (depth u) j) := by
  calc
    _ = FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k
          (FlatAffineLevelRecordData.data (levels midpoint P depth old level (levelQuery u k j.val))) :=
      level_raw P (childDepth midpoint depth) (objective midpoint depth old) (levels midpoint P depth old level) u k j
    _ = FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k
        (FlatAffineLevelRecordData.data (FlatAffineFrozenLevelRecord.freeze (depth u) (level (levelQuery u (depth u) j.val)))) :=
      congrArg (fun r => FlatAffineLevelRecordData.decode (P.dim u + 4) 2 k (FlatAffineLevelRecordData.data r))
        (levels_copy midpoint P depth old level u k j.val hk hj)
    _ = FlatAffineCriticalTower.Level.extend hk
        (FlatAffineLevelRecordData.decode (P.dim u + 4) 2 (depth u)
          (FlatAffineLevelRecordData.data (level (levelQuery u (depth u) j.val)))) :=
      FlatAffineFrozenLevelRecord.decode_freeze (P.dim u + 4) 2 (depth u) k hk _
    _ = _ := congrArg (FlatAffineCriticalTower.Level.extend hk) (level_raw P depth old level u (depth u) j).symm

theorem newest_selected (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    (CoordinateAffineTower.selected P (objective midpoint depth old) u (childDepth midpoint depth u)).val =
      coordinate P depth old u + 1 := by
  change min (objective midpoint depth old (stage u (childDepth midpoint depth u))) (P.dim u + 3) = _
  rw [objective_newest]
  unfold coordinate
  omega

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
