/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcher
/-! # Out-of-range virtual block entries are the native zero branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualUpperBits
set_option backward.isDefEq.respectTransparency false

private theorem integerEntry_outside {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ)
    (h : ¬ (r < n ∧ t < n)) : IntegralCriticalTotalSnapshotBits.integerEntry M r t = 0 := by
  by_cases hr : r < n
  · have ht : ¬ t < n := fun ht => h ⟨hr, ht⟩
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_left hr, dite_eq_right ht]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_right hr]

theorem reduction_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬ finiteAxes P (reductionSize P F) q) : IntegralMixedVirtualMatrixBits.reductionEntry P F q = [] := by
  unfold IntegralMixedVirtualMatrixBits.reductionEntry
  rw [IntegralMixedVirtualMatrixBits.reduction_snapshot, integerEntry_outside _ _ _ h]
  simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem action_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬ finiteAxes P (reductionSize P F) q) : IntegralMixedVirtualMatrixBits.actionEntry P F q = [] := by
  unfold IntegralMixedVirtualMatrixBits.actionEntry
  rw [IntegralMixedVirtualMatrixBits.action_snapshot, integerEntry_outside _ _ _ h]
  simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem factor_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬ finiteAxes P (factorSize P F) q) : IntegralMixedVirtualMatrixBits.relativeFactor P F q = [] := by
  unfold IntegralMixedVirtualMatrixBits.relativeFactor
  rw [IntegralMixedVirtualMatrixBits.power_snapshot, integerEntry_outside _ _ _ h]
  simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits
