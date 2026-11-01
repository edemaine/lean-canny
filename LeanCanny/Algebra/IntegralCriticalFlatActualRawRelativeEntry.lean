/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualRelativeFactor
/-! # Finite phase-twenty-four children read the raw actual factor model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualRawRelativeEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic IntegralCriticalTotalCreatingBits.atFamily
  IntegralCriticalTotalSnapshotBits.modularPowerEntry IntegralCriticalTotalSnapshotBits.powerEntry

theorem child_value (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin (powerDimension (characteristic F) c)) :
    IntegralCriticalFlatActualRelativeFactorBits.value F (IntegralCriticalFlatActualRelativeEntryBits.child F c i.val j.val) =
      residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod ((characteristic F).modulus c)) := by
  let q := IntegralCriticalFlatActualRelativeEntryBits.child F c i.val j.val
  have HR := IntegralCriticalFlatActualRelativeEntryBits.child_root F c i.val j.val
  have HB := IntegralCriticalFlatActualRelativeEntryBits.child_birth F c i.val j.val
  have HM := IntegralCriticalFlatActualRelativeEntryBits.child_modulus F c i.val j.val
  have HI : get F.toParameters .row q = i.val := by
    simp only [q, IntegralCriticalFlatActualRelativeEntryBits.child, IntegralCriticalFlatMatrixQuery.writer_get,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (i.isLt.le.trans (IntegralCriticalActualCaps.coefficient_block_cap F c hv))
  have HJ : get F.toParameters .col q = j.val := by
    simp only [q, IntegralCriticalFlatActualRelativeEntryBits.child, IntegralCriticalFlatMatrixQuery.writer_get,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (j.isLt.le.trans (IntegralCriticalActualCaps.coefficient_block_cap F c hv))
  change IntegralCriticalTotalSnapshotBits.modularPowerEntry F q (get F.toParameters .row q) (get F.toParameters .col q) = _
  rw [HI, HJ, IntegralCriticalTotalSnapshotBits.modularPowerEntry_invariance F q c HR HB HM]
  exact (IntegralCriticalTotalSnapshotBits.modularPowerEntry_fin F c i j).trans
    (congrArg (fun m : ℕ => residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod m))
      (characteristic_modulus F c).symm)

theorem child_valid (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) (i j : ℕ) :
    IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatActualRelativeEntryBits.child F c i j) := by
  change birth F.toParameters (IntegralCriticalFlatActualRelativeEntryBits.child F c i j) <
    (F.rules (RankedHistoryTask.root (IntegralCriticalFlatActualRelativeEntryBits.child F c i j))).length
  rw [IntegralCriticalFlatActualRelativeEntryBits.child_root, IntegralCriticalFlatActualRelativeEntryBits.child_birth]
  exact hv

theorem replies (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalFlatActualRelativeBits.RepliesAt F (IntegralCriticalFlatActualRelativeFactorBits.value F) c :=
  fun i j => child_value F c hv i j

end LeanCanny.Algebra.IntegralCriticalFlatActualRawRelativeEntryBits
