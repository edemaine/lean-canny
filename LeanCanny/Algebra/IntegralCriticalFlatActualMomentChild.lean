/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalMomentValueSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatActualDiagonal
/-! # Actual relative-factor moment children retain the creating matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualMomentChildBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily
  IntegralCriticalTotalMomentValueSnapshotBits.atValue

theorem child_value_bounded (F : Scripts) (p : List Bool)
    (hr : Nat.fromBitsLE (basisRowCode p) ≤ numericCap F.toParameters (RankedHistoryTask.root (original p)))
    (ht : Nat.fromBitsLE (basisColCode p) ≤ numericCap F.toParameters (RankedHistoryTask.root (original p)))
    (hs : Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p) ≤ numericCap F.toParameters (RankedHistoryTask.root (original p)))
    (hu : Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p) ≤ numericCap F.toParameters (RankedHistoryTask.root (original p))) :
    IntegralCriticalTotalMomentValueSnapshotBits.value F (IntegralCriticalFlatBerkowitzQuery.momentWriter F.toParameters p) =
      (momentFamily (characteristic F)).value p := by
  let q := IntegralCriticalFlatBerkowitzQuery.momentWriter F.toParameters p
  have HR : IntegralCriticalFlatHeightBits.root q = IntegralCriticalFlatHeightBits.root (original p) := by
    change RankedHistoryTask.root q = RankedHistoryTask.root (original p)
    exact IntegralCriticalFlatBerkowitzQuery.momentWriter_root _ _
  have HB := IntegralCriticalFlatBerkowitzQuery.momentWriter_birth F.toParameters p
  have HM := IntegralCriticalFlatBerkowitzQuery.momentWriter_modulus F.toParameters p
  rw [IntegralCriticalTotalMomentValueSnapshotBits.value_snapshot,
    IntegralCriticalTotalMomentValueSnapshotBits.native_snapshot]
  apply IntegralCriticalTotalMomentValueSnapshotBits.atValue_congr
  · exact IntegralCriticalTotalCreatingBits.atFamily_invariance F q (original p) HR HB
  · simpa only [q, IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hr
  · simpa only [q, IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left ht
  · simpa only [q, IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hs
  · simpa only [q, IntegralCriticalFlatBerkowitzQuery.momentWriter_get, reduceCtorEq, ite_true, ite_false] using min_eq_left hu
  · exact HM

theorem child_value (F : Scripts) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c) :
    IntegralCriticalTotalMomentValueSnapshotBits.value F
      (IntegralCriticalFlatBerkowitzQuery.momentWriter F.toParameters
        (outerPacket (characteristic F) (IntegralCriticalFlatRelativeFactorBits.packet F.toParameters c))) =
      (momentFamily (characteristic F)).value
        (outerPacket (characteristic F) (IntegralCriticalFlatRelativeFactorBits.packet F.toParameters c)) := by
  apply child_value_bounded
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisRowCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.mod_lt _ ((characteristic F).rank_pos c)).le.trans (IntegralCriticalActualCaps.rank_cap F c hv)
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet, basisColCode,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.mod_lt _ ((characteristic F).rank_pos c)).le.trans (IntegralCriticalActualCaps.rank_cap F c hv)
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le F.toParameters .row c)
  · simp only [outerPacket, IntegralCriticalFlatRelativeFactorBits.packet,
      IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (Nat.div_le_self _ _).trans (get_le F.toParameters .col c)

end LeanCanny.Algebra.IntegralCriticalFlatActualMomentChildBits
