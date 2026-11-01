/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightTableQuery
/-! # Actual retained-reference requests remain finite and select scalar0/2 -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTableQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

theorem birth_le_cap (P : Parameters) (q : List Bool) : birth P q ≤ numericCap P (RankedHistoryTask.root q) :=
  (min_le_right _ _).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1

theorem writer_index (P : Parameters) (q : List Bool) (i : ℕ) (hi : i < birth P q) :
    get P .sourceIndex (writer P (pair q (BinaryNatCode.encode i))) = i := by
  rw [writer_get]
  exact min_eq_left (hi.le.trans (birth_le_cap P q))

theorem writer_row (P : Parameters) (q : List Bool) (i : ℕ) :
    get P .row (writer P (pair q (BinaryNatCode.encode i))) = oldRow P q := by rw [writer_get]; rfl

theorem writer_col (P : Parameters) (q : List Bool) (i : ℕ) :
    get P .col (writer P (pair q (BinaryNatCode.encode i))) = oldCol P q := by rw [writer_get]; rfl

theorem writer_dimension (P : Parameters) (q : List Bool) (i : ℕ) :
    IntegralMixedOldHeightBits.dimension P (writer P (pair q (BinaryNatCode.encode i))) = IntegralMixedOldHeightBits.dimension P q := by
  rw [IntegralMixedOldHeightBits.dimension, writer_birth, writer_root]
  rfl

theorem oldRow_lt (P : Parameters) (q : List Bool) : oldRow P q < IntegralMixedOldHeightBits.dimension P q :=
  Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)

theorem oldCol_lt (P : Parameters) (q : List Bool) : oldCol P q < IntegralMixedOldHeightBits.dimension P q :=
  Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)

theorem writer_valid (P : Parameters) (q : List Bool) (i : ℕ) (hi : i < birth P q) :
    IntegralMixedOldHeightBits.valid P (writer P (pair q (BinaryNatCode.encode i))) := by
  unfold IntegralMixedOldHeightBits.valid
  rw [writer_index P q i hi, writer_birth, writer_row, writer_col, writer_dimension]
  exact ⟨hi, oldRow_lt P q, oldCol_lt P q⟩

theorem writer_task_valid (P : Parameters) (q : List Bool) (i : ℕ) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedVirtualCaps.valid P (writer P (pair q (BinaryNatCode.encode i))) := by
  unfold IntegralMixedVirtualCaps.valid at hv ⊢
  rw [writer_birth, writer_root]
  exact hv

theorem writer_selected (P : Parameters) (q : List Bool) (i : ℕ) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedNativeOldHeightBits.selected P (writer P (pair q (BinaryNatCode.encode i))) = true := by
  apply (IntegralMixedNativeOldHeightBits.selected_iff P _).mpr
  refine ⟨writer_task_valid P q i hv, writer_routine P q i, ?_⟩
  exact writer_phase P q i

end LeanCanny.Algebra.IntegralMixedHeightTableQueryBits
