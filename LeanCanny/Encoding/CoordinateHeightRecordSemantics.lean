/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightSemantics
public import LeanCanny.Encoding.FlatAffineLevelRecordData

/-! # Exact slice levels of native coordinate records

The copied-height record evaluates to twice its retained coordinate. The
midpoint record evaluates to the sum of its two retained coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateHeightRecord
open LeanCanny.Algebra
open FlatAffineFullSourceTower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem decode_data (n k : ℕ) (bits : List Bool) :
    FlatAffineLevelRecordData.decode n 2 k (FlatAffineLevelRecordData.data bits) = decode n k bits := rfl

theorem data_decode_height (n index ancestor m : ℕ) (ha : ancestor < m) :
    FlatAffineLevelRecordData.decode n 2 m (FlatAffineLevelRecordData.data (height n index ancestor)) =
      FlatAffineCriticalTower.Level.height ⟨ancestor, ha⟩ (fun i : Fin n => if i.val = index then 2 else 0) :=
  (decode_data n m _).trans (decode_height n index m ⟨ancestor, ha⟩)

theorem data_decode_midpoint (n index left right m : ℕ) (hl : left < m) (hr : right < m) :
    FlatAffineLevelRecordData.decode n 2 m (FlatAffineLevelRecordData.data (midpoint n index left right)) =
      FlatAffineCriticalTower.Level.midpoint ⟨left, hl⟩ ⟨right, hr⟩
        (fun i : Fin n => if i.val = index then 1 else 0) :=
  (decode_data n m _).trans (decode_midpoint n index m ⟨left, hl⟩ ⟨right, hr⟩)

theorem eval_height {n m : ℕ} (index : Fin n) (ancestor : Fin m)
    (z : FlatAffineCriticalTower.Ancestors n m → ℝ) :
    (FlatAffineLevelRecordData.decode n 2 m
      (FlatAffineLevelRecordData.data (height n index.val ancestor.val))).polynomial.eval₂ (Int.castRingHom ℝ) z =
      2 * z (FlatAffineCriticalTower.oldAmbient m ancestor index) := by
  rw [data_decode_height n index.val ancestor.val m ancestor.isLt, FlatAffineCriticalTower.Level.eval_height]
  simp [← Fin.ext_iff, ite_mul]

theorem eval_midpoint {n m : ℕ} (index : Fin n) (left right : Fin m)
    (z : FlatAffineCriticalTower.Ancestors n m → ℝ) :
    (FlatAffineLevelRecordData.decode n 2 m
      (FlatAffineLevelRecordData.data (midpoint n index.val left.val right.val))).polynomial.eval₂ (Int.castRingHom ℝ) z =
      z (FlatAffineCriticalTower.oldAmbient m left index) + z (FlatAffineCriticalTower.oldAmbient m right index) := by
  rw [data_decode_midpoint n index.val left.val right.val m left.isLt right.isLt,
    FlatAffineCriticalTower.Level.eval_midpoint]
  simp [← Fin.ext_iff, ite_mul]

end LeanCanny.Encoding.CoordinateHeightRecord
