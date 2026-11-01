/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualMoment
public import LeanCanny.Algebra.IntegralCriticalFlatActualAction
/-! # Typed moment row, column and interior routes read the actual action matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily
  IntegralCriticalTotalSnapshotBits.modularActionEntry IntegralCriticalTotalSnapshotBits.actionEntry

noncomputable abbrev actionValue := IntegralCriticalFlatActualActionBits.value

theorem actionChild_value (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin ((characteristic F).dimension c)) (r t : Fin ((characteristic F).rank c)) :
    actionValue F (IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic F).entryMatrix c i j r t : ℤ) : ZMod ((characteristic F).modulus c)) := by
  let p := pair (IntegralBlockMomentBits.context c r.val t.val)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  let q := IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F) p
  have HP : original p = c := by simp only [p, original, IntegralBlockMomentBits.context, pairFst_pair]
  have HR : IntegralCriticalFlatHeightBits.root q = IntegralCriticalFlatHeightBits.root c := by
    change RankedHistoryTask.root q = RankedHistoryTask.root c
    exact (IntegralCriticalFlatBerkowitzQuery.entryWriter_root _ _ p).trans (congrArg RankedHistoryTask.root HP)
  have HB : birth F.toParameters q = birth F.toParameters c := by
    change birth F.toParameters (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F) p)) = _
    rw [IntegralCriticalFlatMatrixQuery.writer_birth, IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c := by
    change IntegralCriticalHistoryTask.modulus F.toParameters (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F) p)) = _
    rw [IntegralCriticalFlatMatrixQuery.writer_modulus, IntegralCriticalFlatBerkowitzQuery.entry_parent, HP]
  let u : Fin ((characteristic F).dimension c * (characteristic F).rank c) := finProdFinEquiv (i, r)
  let v : Fin ((characteristic F).dimension c * (characteristic F).rank c) := finProdFinEquiv (j, t)
  have HI : get F.toParameters .row q = u.val := by
    change get F.toParameters .row (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F) p)) = _
    simp only [IntegralCriticalFlatMatrixQuery.writer_get, IntegralCriticalFlatBerkowitzQuery.entryPacket,
      p, original, IntegralBlockMomentBits.context, basisRowCode, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (u.isLt.le.trans (IntegralCriticalActualCaps.action_block_cap F c hv))
  have HJ : get F.toParameters .col q = v.val := by
    change get F.toParameters .col (IntegralCriticalFlatMatrixQuery.writer F.toParameters .actionEntry
      (IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic F) p)) = _
    simp only [IntegralCriticalFlatMatrixQuery.writer_get, IntegralCriticalFlatBerkowitzQuery.entryPacket,
      p, original, IntegralBlockMomentBits.context, basisColCode, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (v.isLt.le.trans (IntegralCriticalActualCaps.action_block_cap F c hv))
  change IntegralCriticalTotalSnapshotBits.modularActionEntry F q (get F.toParameters .row q) (get F.toParameters .col q) = _
  rw [HI, HJ, IntegralCriticalTotalSnapshotBits.modularActionEntry_invariance F q c HR HB HM]
  have HE := IntegralCriticalFlatActualActionBits.finite_value F c u v
  let := (characteristic F).ring c
  have HX : IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic F) c u v =
      (characteristic F).entryMatrix c i j r t :=
    IntegralCoefficientBlocks.block_entry ((characteristic F).basis c) ((characteristic F).matrix c) i j r t
  exact HE.trans ((congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c))) HX).trans
    (congrArg (fun m : ℕ => residueBits (((characteristic F).entryMatrix c i j r t : ℤ) : ZMod m))
      (characteristic_modulus F c).symm))

end LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
