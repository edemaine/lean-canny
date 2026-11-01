/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalMomentSnapshot
public import LeanCanny.Algebra.IntegralCriticalActualCaps
/-! # Actual moment-power children read the retained augmented matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily
  IntegralBlockMomentBits.Family.powerMatrix

noncomputable abbrev moment (F : Scripts) := IntegralCriticalFlatMomentBits.source F.toParameters (characteristic F)

noncomputable def value (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalTotalMomentSnapshotBits.modularEntry F c
    (get F.toParameters .row c % IntegralCriticalTotalMomentSnapshotBits.size F c)
    (get F.toParameters .col c % IntegralCriticalTotalMomentSnapshotBits.size F c)

theorem size_pos (F : Scripts) (c : List Bool) : 0 < IntegralCriticalTotalMomentSnapshotBits.size F c := by
  have HE : (moment F).rank c = (characteristic F).rank c := by
    change (characteristic F).rank (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet F.toParameters c)) = _
    rw [IntegralCriticalFlatMomentBits.packet_parent]
  have HR : 0 < (moment F).rank c := HE.symm ▸ (characteristic F).rank_pos c
  change 0 < ((moment F).dimension c + 2) * (moment F).rank c
  exact Nat.mul_pos (by omega) HR

theorem moment_modulus (F : Scripts) (c : List Bool) :
    (moment F).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c := by
  change (characteristic F).modulus
    (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet F.toParameters c)) = _
  rw [IntegralCriticalFlatMomentBits.packet_parent, characteristic_modulus]

attribute [local irreducible] IntegralCriticalTotalMomentSnapshotBits.modularEntry

theorem program_value (F : Scripts) (h : Controls F) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralCriticalFlatMomentEntryBits.RepliesAt F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h) answer c) :
    (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).value answer c = value F c := by
  rw [IntegralCriticalFlatMomentEntryBits.value _ _ _ _ answer c he]
  let r : Fin (IntegralCriticalTotalMomentSnapshotBits.size F c) := ⟨get F.toParameters .row c % IntegralCriticalTotalMomentSnapshotBits.size F c, Nat.mod_lt _ (size_pos F c)⟩
  let t : Fin (IntegralCriticalTotalMomentSnapshotBits.size F c) := ⟨get F.toParameters .col c % IntegralCriticalTotalMomentSnapshotBits.size F c, Nat.mod_lt _ (size_pos F c)⟩
  have HE := IntegralBlockMomentBits.entry_correct (moment F)
    (IntegralCriticalFlatMomentBits.access F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)) c r t
  have HM := congrArg (fun m : ℕ => residueBits (((moment F).powerMatrix c r t : ℤ) : ZMod m)) (moment_modulus F c)
  exact HE.trans (HM.trans (IntegralCriticalTotalMomentSnapshotBits.modularEntry_fin F c r t).symm)

def child (F : Scripts) (c : List Bool) (i j : ℕ) : List Bool :=
  IntegralCriticalFlatMatrixQuery.writer F.toParameters .momentEntry
    (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)))

theorem child_value (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin (IntegralCriticalTotalMomentSnapshotBits.size F c)) :
    value F (child F c i.val j.val) =
      residueBits (((moment F).powerMatrix c i j : ℤ) : ZMod ((moment F).modulus c)) := by
  let q := child F c i.val j.val
  have HR : IntegralCriticalFlatHeightBits.root q = IntegralCriticalFlatHeightBits.root c := by
    simpa only [q, child, pairFst_pair, IntegralCriticalFlatHeightBits.root] using IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HB : birth F.toParameters q = birth F.toParameters c := by
    simpa only [q, child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c := by
    simpa only [q, child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HS : get F.toParameters .slot11 q = get F.toParameters .slot11 c := by
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HT : get F.toParameters .slot12 q = get F.toParameters .slot12 c := by
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HD := IntegralCriticalTotalMomentSnapshotBits.size_invariance F q c HR HB HS HT
  have HI : get F.toParameters .row q = i.val := by
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (i.isLt.le.trans (IntegralCriticalActualCaps.moment_block_cap F c hv))
  have HJ : get F.toParameters .col q = j.val := by
    simp only [q, child, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (j.isLt.le.trans (IntegralCriticalActualCaps.moment_block_cap F c hv))
  unfold value
  rw [HI, HJ, HD, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
  have HE := (IntegralCriticalTotalMomentSnapshotBits.modularEntry_invariance F q c HR HB HS HT HM i.val j.val).trans
    (IntegralCriticalTotalMomentSnapshotBits.modularEntry_fin F c i j)
  exact HE.trans (congrArg (fun m : ℕ => residueBits (((moment F).powerMatrix c i j : ℤ) : ZMod m))
    (moment_modulus F c).symm)

theorem replies (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalFlatMomentBits.RepliesAt F.toParameters (characteristic F) (value F) c :=
  fun i j => child_value F c hv i j

end LeanCanny.Algebra.IntegralCriticalFlatActualMomentBits
