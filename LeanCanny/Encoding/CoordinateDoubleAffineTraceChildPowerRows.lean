/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildRows

/-! # Extended histories preserve every powered child equation -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate FlatAffinePowerPositive.system

theorem extended_power_system (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q) :
    FlatAffinePowerPositive.system (extendedInputs midpoint P d old level) q =
      FlatAffinePowerPositive.system
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q := by
  have hk (t : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q)) :
      t.val ≤ depth d (append midpoint q) := by rw [depth_append]; exact t.isLt.le
  have HS := funext (fun t : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q) =>
    extended_free midpoint P d old level q t.val (hk t))
  have HD := funext (fun t : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q) =>
    extended_direction midpoint P d old level q t.val (hk t))
  have HL := funext (fun t : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q) =>
    funext (extended_level midpoint P d old level q t.val hv (hk t)))
  let build (s : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q) → Finset (Fin ((readers P).dim q + 4)))
      (a : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q) →
        Fin ((readers P).dim q + 4 + 1) → Fin ((readers P).dim q + 4) → ℤ)
      (b : (t : Fin (CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q)) →
        Fin ((readers P).dim q + 4) → FlatAffineCriticalTower.Level ((readers P).dim q + 4) t.val ℤ) :=
    PositivePolynomialSystem.system (FlatAffinePowerTower.system
      (BoundedFullCriticalSamples.polynomial (readers P) q) (FlatAffinePowerControls.degree (extendedInputs midpoint P d old level) q) s a b)
  unfold FlatAffinePowerPositive.system FlatAffinePowerPositive.rawSystem
  change build (fun t => FlatAffineFullSourceTower.free (extendedInputs midpoint P d old level) q t.val)
      (fun t => FlatAffineFullSourceTower.direction (extendedInputs midpoint P d old level) q t.val)
      (fun t => FlatAffineFullSourceTower.level (extendedInputs midpoint P d old level) q t.val) =
    build (fun t => FlatAffineFullSourceTower.free
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q t.val)
      (fun t => FlatAffineFullSourceTower.direction
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q t.val)
      (fun t => FlatAffineFullSourceTower.level
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q t.val)
  rw [HS, HD, HL]

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
