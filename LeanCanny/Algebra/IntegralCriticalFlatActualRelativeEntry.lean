/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualRelative
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorLocal
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
public import LeanCanny.Algebra.IntegralCriticalActualCaps
/-! # Actual relative-power children retain the parent matrix

Finite indices fit the source cap. Fresh factor words therefore read back
those exact indices, and their integer matrices agree with the parent's
matrix by the root and birth snapshot invariant.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualRelativeEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess entryProgram Source.powerMatrix
  IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalTotalSnapshotBits.modularPowerEntry
  IntegralCriticalTotalSnapshotBits.powerEntry

noncomputable def value (F : Scripts) (h : Controls F) (c : List Bool) : List Bool :=
  entryProgram (characteristic F) (characteristicAccess F h)
    (IntegralCriticalFlatRelativeFactorBits.packet F.toParameters c)

def child (F : Scripts) (c : List Bool) (i j : ℕ) : List Bool :=
  IntegralCriticalFlatMatrixQuery.writer F.toParameters .relativeFactor
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem child_root (F : Scripts) (c : List Bool) (i j : ℕ) :
    RankedHistoryTask.root (child F c i j) = RankedHistoryTask.root c := by
  simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .relativeFactor
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem child_birth (F : Scripts) (c : List Bool) (i j : ℕ) :
    birth F.toParameters (child F c i j) = birth F.toParameters c := by
  simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters .relativeFactor
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem child_modulus (F : Scripts) (c : List Bool) (i j : ℕ) :
    IntegralCriticalHistoryTask.modulus F.toParameters (child F c i j) = IntegralCriticalHistoryTask.modulus F.toParameters c := by
  simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters .relativeFactor
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem child_value (F : Scripts) (h : Controls F) (c : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin (powerDimension (characteristic F) c)) :
    value F h (child F c i.val j.val) =
      residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod ((characteristic F).modulus c)) := by
  let q := child F c i.val j.val
  have HR : RankedHistoryTask.root q = RankedHistoryTask.root c := child_root F c i.val j.val
  have HB : birth F.toParameters q = birth F.toParameters c := child_birth F c i.val j.val
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c :=
    child_modulus F c i.val j.val
  have HD := IntegralCriticalTotalSnapshotBits.powerDimension_invariance F q c HR HB
  let r : Fin (powerDimension (characteristic F) q) := ⟨i.val, by rw [HD]; exact i.isLt⟩
  let t : Fin (powerDimension (characteristic F) q) := ⟨j.val, by rw [HD]; exact j.isLt⟩
  have HI : get F.toParameters .row q = i.val := by
    have H := IntegralCriticalActualCaps.coefficient_block_cap F c hv
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (Nat.le_trans (Nat.le_of_lt i.isLt) H)
  have HJ : get F.toParameters .col q = j.val := by
    have H := IntegralCriticalActualCaps.coefficient_block_cap F c hv
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (Nat.le_trans (Nat.le_of_lt j.isLt) H)
  have HE := entry_correct (characteristic F) (characteristicAccess F h) q r t
  have HV : value F h q = IntegralCriticalTotalSnapshotBits.modularPowerEntry F q i.val j.val := by
    rw [value, IntegralCriticalFlatRelativeFactorBits.packet, HI, HJ]
    have HMbits := congrArg (fun m : ℕ => residueBits (((characteristic F).powerMatrix q r t : ℤ) : ZMod m))
      (characteristic_modulus F q)
    exact (HE.trans HMbits).trans (IntegralCriticalTotalSnapshotBits.modularPowerEntry_fin F q r t).symm
  have HMbits := congrArg (fun m : ℕ => residueBits (((characteristic F).powerMatrix c i j : ℤ) : ZMod m))
    (characteristic_modulus F c)
  exact (HV.trans (IntegralCriticalTotalSnapshotBits.modularPowerEntry_retarget_fin F c q HR.symm HB.symm HM.symm i j)).trans HMbits.symm

theorem replies (F : Scripts) (h : Controls F) (c : List Bool)
    (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalFlatActualRelativeBits.RepliesAt F (value F h) c :=
  fun i j => child_value F h c hv i j

end LeanCanny.Algebra.IntegralCriticalFlatActualRelativeEntryBits
