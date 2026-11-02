/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscNativeCharacteristic
public import LeanCanny.Algebra.IntegralMixedPscNativeFactor
/-! # Invalid natural labels are zero in the actual PSC matrix components -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical

private theorem outside {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ) (h : ¬(r < n ∧ t < n)) :
    IntegralCriticalTotalSnapshotBits.integerEntry M r t = 0 := by
  by_cases hr : r < n
  · have ht : ¬t < n := fun ht => h ⟨hr, ht⟩
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_left hr, dite_eq_right ht]
  · simp only [IntegralCriticalTotalSnapshotBits.integerEntry, dite_eq_right hr]

theorem entry_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬(get P .row q < IntegralMixedPscMomentMatrix.size P F q ∧
      get P .col q < IntegralMixedPscMomentMatrix.size P F q)) : entryValue P F q = [] := by
  have H := outside ((moment P F).powerMatrix q) (get P .row q) (get P .col q) h
  exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans
    (by simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])

theorem factor_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬(get P .row q < factorSize P F q ∧ get P .col q < factorSize P F q)) :
    factorValue P F q = [] := by
  have H := outside ((characteristic P F).powerMatrix q) (get P .row q) (get P .col q) h
  have HE := congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    ((IntegralMixedPscMatrixModel.power_snapshot P F q (get P .row q) (get P .col q)).trans H)
  exact HE.trans (by simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])

theorem characteristic_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬(get P .row q < (characteristic P F).rank q ∧ get P .col q < (characteristic P F).rank q)) :
    characteristicValue P F q = [] := by
  have H := outside ((characteristic P F).coefficientMatrix q 0) (get P .row q) (get P .col q) h
  exact (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H).trans
    (by simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])

end LeanCanny.Algebra.IntegralMixedPscUpperBits
