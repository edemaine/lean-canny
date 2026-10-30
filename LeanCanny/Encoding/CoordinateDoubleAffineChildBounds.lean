/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildLevels

/-! # Decreasing coordinate rank and shared ancestry budgets

Either child adds at most two retained critical blocks and uses one fewer
free coordinate. The sum of the depth and twice the remaining rank does not
increase. This bounds shared ancestry without duplicating ancestral systems.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (stage)
set_option backward.isDefEq.respectTransparency false

def rank (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) : ℕ :=
  P.dim u + 3 - coordinate P depth old u

theorem rank_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) : UnaryFn (rank P depth old) :=
  (hP.dim.add (UnaryFn.const 3)).sub (coordinate_unary hP hd ho)

theorem coordinate_step (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    coordinate P (childDepth midpoint depth) (objective midpoint depth old) u = coordinate P depth old u + 1 :=
  newest_selected midpoint P depth old u hn

theorem rank_step (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    rank P depth old u = rank P (childDepth midpoint depth) (objective midpoint depth old) u + 1 := by
  unfold rank
  rw [coordinate_step midpoint P depth old u hn]
  unfold coordinate
  omega

theorem rank_decreases (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    rank P (childDepth midpoint depth) (objective midpoint depth old) u < rank P depth old u := by
  rw [rank_step midpoint P depth old u hn]
  omega

theorem ancestry_budget (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    childDepth midpoint depth u + 2 * rank P (childDepth midpoint depth) (objective midpoint depth old) u ≤
      depth u + 2 * rank P depth old u := by
  rw [rank_step midpoint P depth old u hn]
  have hc : copies midpoint ≤ 2 := by cases midpoint <;> decide
  unfold childDepth
  omega

theorem count_le_budget (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (hn : old (stage u (depth u)) < P.dim u + 3) :
    FlatAffineFullSourceTower.count (inputs midpoint P depth old level) u ≤
      (depth u + 2 * rank P depth old u) * (2 * (P.dim u + 4) + 1) := by
  have H := ancestry_budget midpoint P depth old u hn
  have hd : childDepth midpoint depth u ≤ depth u + 2 * rank P depth old u := by omega
  change childDepth midpoint depth u * FlatAffineCriticalTower.width (P.dim u + 4) ≤ _
  have hw : FlatAffineCriticalTower.width (P.dim u + 4) = 2 * (P.dim u + 4) + 1 := by
    unfold FlatAffineCriticalTower.width
    omega
  rw [hw]
  exact Nat.mul_le_mul_right _ hd

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
