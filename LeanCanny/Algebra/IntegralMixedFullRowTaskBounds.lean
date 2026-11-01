/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueRestoredSource

/-! # The restored-row lower target fits the original scalar and task caps

The native repacking writes exactly the canonical critical-grid width.
Its target therefore lies below the spatial coordinate degree, already
bounded by the one initial scalar cap. This bound applies even when the
incoming monomial fails the support guard or contains oversized exponents.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowTaskBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualSweepSource IntegralMixedVirtualCaps

theorem lowTarget_lt (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFullRowMultiplier.lowTarget F I W q <
      IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q) := by
  unfold IntegralMixedFullRowMultiplier.lowTarget IntegralMixedFullRowMultiplier.packet IntegralMixedFullRowMultiplier.target
  rw [CoefficientWidthBits.packed_packet]
  have H := Nat.fromBitsLE_lt_pow_length
    (FixedWidthNatVector.encode (IntegralMixedFullRowMultiplier.free F q)
      (IntegralMixedFullRowMultiplier.canonicalWidth F q)
      (fun i => if i < IntegralMixedFullRowMultiplier.free F q then entry (W q) (I.target q) i else 0))
  rw [FixedWidthNatVector.length_encode] at H
  convert H using 1
  simp only [IntegralMixedCoordinateSquarefree.coordinateDegree, PurePowerReductionBounds.dimension, count,
    ← pow_mul, IntegralMixedFullRowMultiplier.canonicalWidth, Nat.mul_comm]

theorem lowTarget_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (W : List Bool → ℕ) (q : List Bool) :
    IntegralMixedFullRowMultiplier.lowTarget (IntegralMixedVirtualTaskBits.family P F)
      (IntegralMixedVirtualTaskBits.indices P F) W q ≤ numericCap P (RankedHistoryTask.root q) :=
  ((lowTarget_lt _ _ W q).trans (IntegralMixedValueTaskBounds.coordinateDegree_lt_scalar
    (IntegralMixedVirtualTaskBits.family P F) q)).le.trans
      (IntegralMixedValueTaskBounds.scalar_le_root_cap P F h q)

theorem coordinate_cap (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    ((IntegralMixedVirtualTaskBits.indices P F).coordinate q).val ≤ numericCap P (RankedHistoryTask.root q) :=
  (((IntegralMixedVirtualTaskBits.indices P F).coordinate q).isLt.trans
    (IntegralMixedValueTaskBounds.free_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q)).le.trans
      (IntegralMixedValueTaskBounds.scalar_le_root_cap P F h q)

end LeanCanny.Algebra.IntegralMixedFullRowTaskBounds
