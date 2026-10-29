/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourcePositive
public import LeanCanny.Algebra.FlatAffineCriticalIndexedRows

/-! # Total stage-order coordinates for positive affine row dispatch

Clamping gives total coordinates even for the dummy row of an empty tower.
On original rows the coordinates are exactly the unchanged ancestral indices.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowLayout
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))

def index (u : List Bool) : ℕ := (row u).val
def stage (u : List Bool) : ℕ := index F row u / stageWidth F u
def slot (u : List Bool) : ℕ := index F row u % stageWidth F u
def offset (u : List Bool) : ℕ := stage F row u * stageWidth F u

theorem arity_pos (u : List Bool) : 0 < arity F u := by unfold arity; omega
theorem width_pos (u : List Bool) : 0 < stageWidth F u := by
  change 0 < arity F u + (arity F u + 1)
  omega

def spatial (u : List Bool) : Fin (arity F u) :=
  ⟨min (slot F row u) (arity F u - 1), by have := arity_pos F u; omega⟩
def height (u : List Bool) : Fin (arity F u) :=
  ⟨min (slot F row u - arity F u - 1) (arity F u - 1), by have := arity_pos F u; omega⟩

def coordinate (u : List Bool) (k j : ℕ) : Fin (FlatAffineFullSourcePositive.count F u) :=
  ⟨min (k * stageWidth F u + j) (FlatAffineFullSourceTower.count F u), by
    change min _ _ < FlatAffineFullSourceTower.count F u + 1
    omega⟩

def current (u : List Bool) (i : Fin (arity F u)) := coordinate F u (stage F row u) i.val
def multiplier (u : List Bool) (j : Fin (arity F u + 1)) :=
  coordinate F u (stage F row u) (arity F u + j.val)

def directionRecord (u : List Bool) : List Bool := F.direction (FlatAffineFullSourceTower.stage u (stage F row u))
def levelRecord (u : List Bool) : List Bool :=
  F.level (FlatAffineFullSourceTower.levelQuery u (stage F row u) (height F row u).val)

def oldLeft (u : List Bool) : ℕ := min (Nat.fromBitsLE (FlatAffineFullSourceTower.left (levelRecord F row u))) (stage F row u - 1)
def oldRight (u : List Bool) : ℕ := min (Nat.fromBitsLE (FlatAffineFullSourceTower.right (levelRecord F row u))) (stage F row u - 1)

theorem split_index (u : List Bool) : offset F row u + slot F row u = index F row u := by
  unfold offset slot stage
  simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (index F row u) (stageWidth F u)

theorem stage_lt (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u) :
    stage F row u < F.depth u :=
  (Nat.div_lt_iff_lt_mul (width_pos F u)).mpr h

theorem block_fit (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u) :
    offset F row u + stageWidth F u ≤ FlatAffineFullSourceTower.count F u := by
  have H := Nat.mul_le_mul_right (stageWidth F u) (stage_lt F row u h)
  simpa only [Nat.succ_mul, offset, FlatAffineFullSourceTower.count] using H

theorem coordinate_current (u : List Bool) (k : ℕ) (hk : k < F.depth u) (i : Fin (arity F u)) :
    coordinate F u k i.val = Fin.castSucc (FlatAffineCriticalIndexedRows.current k hk i) := by
  apply Fin.ext
  change min (k * stageWidth F u + i.val) (FlatAffineFullSourceTower.count F u) = _
  have H := Nat.mul_le_mul_right (stageWidth F u) hk
  have hi : i.val < stageWidth F u := i.isLt.trans_le (by change arity F u ≤ arity F u + (arity F u + 1); omega)
  rw [Nat.succ_mul] at H
  rw [Nat.min_eq_left (by change _ ≤ F.depth u * stageWidth F u; omega)]
  rfl

theorem coordinate_multiplier (u : List Bool) (k : ℕ) (hk : k < F.depth u) (j : Fin (arity F u + 1)) :
    coordinate F u k (arity F u + j.val) = Fin.castSucc (FlatAffineCriticalIndexedRows.multiplier k hk j) := by
  apply Fin.ext
  change min (k * stageWidth F u + (arity F u + j.val)) (FlatAffineFullSourceTower.count F u) = _
  have H := Nat.mul_le_mul_right (stageWidth F u) hk
  have hj : arity F u + j.val < stageWidth F u := by change _ < arity F u + (arity F u + 1); omega
  rw [Nat.succ_mul] at H
  rw [Nat.min_eq_left (by change _ ≤ F.depth u * stageWidth F u; omega)]
  rfl

end LeanCanny.Encoding.FlatAffineRowLayout
