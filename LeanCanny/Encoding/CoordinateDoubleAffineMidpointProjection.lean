/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
public import LeanCanny.Algebra.FlatAffinePairedProjection

/-! # Native coordinate indices for sharing paired critical ancestry

The projection retains the full left critical sample and only the right
sample's newest block. Its coordinate program uses the original dimension
and depth controls; no coordinate-index reader is supplied separately.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords (childInput)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def midpointProjection (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    Fin ((childInput true P depth old level).count u) → Fin ((input P depth old level).count u) :=
  FlatAffinePairedProjection.projection (P.dim u + 4) (depth u)

theorem midpoint_width_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime) :
    UnaryFn (fun u => FlatAffineCriticalTower.width (P.dim u + 4)) :=
  (hP.dim.add (UnaryFn.const 4)).add ((hP.dim.add (UnaryFn.const 4)).add (UnaryFn.const 1))

theorem midpoint_old_count_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth : List Bool → ℕ} (hd : UnaryFn depth) :
    UnaryFn (fun u => FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u)) :=
  (hd.add (UnaryFn.const 1)).mul (midpoint_width_unary hP)

theorem midpoint_new_count_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth : List Bool → ℕ} (hd : UnaryFn depth) :
    UnaryFn (fun u => FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u)) :=
  (hd.add (UnaryFn.const 2)).mul (midpoint_width_unary hP)

theorem midpoint_coordinate_val (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u d : List Bool) :
    (SquareSampleProjectedThom.coordinate (input P depth old level) (childInput true P depth old level)
      (midpointProjection P depth old level) u d).val =
      let j := min (Nat.fromBitsLE (LeanCanny.pairFst d)) (FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u))
      if j < FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u) then j else
        if j < FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u) then
          FlatAffinePairedProjection.oldPositive (P.dim u + 4) (depth u) +
            (depth u * FlatAffineCriticalTower.width (P.dim u + 4) +
              (j - FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u)))
        else FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u) := by
  have hj : (SquareSampleInput.selected (childInput true P depth old level) u (LeanCanny.pairFst d)).val =
      min (Nat.fromBitsLE (LeanCanny.pairFst d)) (FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u)) := by
    change min (Nat.fromBitsLE (LeanCanny.pairFst d))
      ((FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u) + 1) - 1) = _
    rw [Nat.add_sub_cancel]
  exact (FlatAffinePairedProjection.projection_val (P.dim u + 4) (depth u)
    (SquareSampleInput.selected (childInput true P depth old level) u (LeanCanny.pairFst d))).trans
      (congrArg (fun j : ℕ => if j < FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u) then j else
        if j < FlatAffinePairedProjection.newCount (P.dim u + 4) (depth u) then
          FlatAffinePairedProjection.oldPositive (P.dim u + 4) (depth u) +
            (depth u * FlatAffineCriticalTower.width (P.dim u + 4) +
              (j - FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u)))
        else FlatAffinePairedProjection.oldCount (P.dim u + 4) (depth u)) hj)

theorem midpoint_coordinate_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool} (hd : UnaryFn depth) :
    UnaryFn (fun q => (SquareSampleProjectedThom.coordinate (input P depth old level) (childInput true P depth old level)
      (midpointProjection P depth old level) (LeanCanny.pairFst q) (LeanCanny.pairSnd q)).val) := by
  have ho := (midpoint_old_count_unary hP hd).comp pairFst_mem_FP
  have hn := (midpoint_new_count_unary hP hd).comp pairFst_mem_FP
  have hi := UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hn
  have hr := (ho.add (UnaryFn.const 1)).add
    (((hd.mul (midpoint_width_unary hP)).comp pairFst_mem_FP).add (hi.sub ho))
  apply (UnaryFn.ite (FPPred.lt hi ho) hi (UnaryFn.ite (FPPred.lt hi hn) hr ho)).of_eq
  intro q
  exact (midpoint_coordinate_val P depth old level (LeanCanny.pairFst q) (LeanCanny.pairSnd q)).symm

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
