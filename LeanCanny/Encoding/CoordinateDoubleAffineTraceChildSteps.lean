/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceInput
public import LeanCanny.Encoding.CoordinateDoubleAffineTraceLevelSteps

/-! # A history extension has exactly the existing recursive child records -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
open FlatAffineFullSourceTower (stage levelQuery)
set_option backward.isDefEq.respectTransparency false

theorem child_coordinate (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (q : List Bool)
    (hv : Valid P (seedCoordinate d old) q) :
    CoordinateDoubleAffineChildRecords.coordinate (readers P) (depth d) (objective d old) q =
      coordinate (seedCoordinate d old) q := by
  rw [CoordinateDoubleAffineChildRecords.coordinate, objective_current]
  exact Nat.min_eq_left hv

theorem child_newLevel (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (q : List Bool)
    (hv : Valid P (seedCoordinate d old) q) :
    CoordinateDoubleAffineChildRecords.newLevel midpoint (readers P) (depth d) (objective d old) q =
      record midpoint (P.dim (base q) + 4) (coordinate (seedCoordinate d old) q) (depth d q) := by
  rw [CoordinateDoubleAffineChildRecords.newLevel, child_coordinate P d old q hv]
  cases midpoint <;> rfl

theorem child_levels_stage (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k j : ℕ) :
    CoordinateDoubleAffineChildRecords.levels midpoint P d old level (levelQuery q k j) =
      if k < d q then level (levelQuery q k j) else
        if k = CoordinateDoubleAffineChildRecords.childDepth midpoint d q ∧
          j = CoordinateDoubleAffineChildRecords.coordinate P d old q then
            CoordinateDoubleAffineChildRecords.newLevel midpoint P d old q else
              FlatAffineFrozenLevelRecord.freeze (d q) (level (levelQuery q (d q) j)) := by
  rw [CoordinateDoubleAffineChildRecords.levels, CoordinateDoubleAffineChildRecords.isNewLevel_at]
  simp only [CoordinateDoubleAffineChildRecords.originalQuery, CoordinateDoubleAffineChildRecords.originalStage,
    levelQuery, stage, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Bool.and_eq_true, decide_eq_true_eq]

theorem levels_append (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (k j : ℕ)
    (hv : Valid P (seedCoordinate d old) q) (hk : k ≤ depth d (append midpoint q)) :
    levels P d old level (levelQuery (append midpoint q) k j) =
      CoordinateDoubleAffineChildRecords.levels midpoint (readers P) (depth d) (objective d old) (levels P d old level)
        (levelQuery q k j) := by
  rw [levels_stage, base_append, history_append, child_levels_stage,
    child_coordinate P d old q hv, child_newLevel midpoint P d old q hv]
  simp only [levels_stage, depth, coordinate, seedCoordinate, CoordinateDoubleAffineChildRecords.childDepth]
  have hk' : k ≤ d (base q) + offset (history q ++ [midpoint]) := by
    simpa only [depth, base_append, history_append] using hk
  have H := levelAt_append (P.dim (base q) + 4) (d (base q)) (seedCoordinate d old (base q))
    (history q) (fun a b => level (levelQuery (base q) a b)) midpoint k j hk'
  rw [offset_append] at H
  simpa only [Nat.add_assoc, seedCoordinate] using H

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
