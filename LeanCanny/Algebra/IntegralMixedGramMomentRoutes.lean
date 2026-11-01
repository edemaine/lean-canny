/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramMomentEntry

/-! # Actual Gram action entries at the three typed augmented-moment routes -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits IntegralMixedGramMatrixModel
open scoped Classical

theorem action_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((characteristic P F).dimension q * (characteristic P F).rank q)) :
    actionValue P F (IntegralCriticalFlatMatrixQuery.writer P .actionEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic P F) q i j : ℤ) : ZMod (modulus P q)) := by
  let c := IntegralCriticalFlatMatrixQuery.writer P .actionEntry
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) :=
    i.isLt.le.trans (IntegralMixedGramCharacteristicBounds.action_cap P F g q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) :=
    j.isLt.le.trans (IntegralMixedGramCharacteristicBounds.action_cap P F g q hv)
  have HS : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q := by
    apply IntegralMixedVirtualTaskBits.saved_invariance
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair]
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair]
  have HC := action_transport P F q c i.val j.val HS
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [action_snapshot] at HC
  exact HC.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin
      (IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic P F) q) i j))

theorem actionChild_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((characteristic P F).dimension q)) (r t : Fin ((characteristic P F).rank q)) :
    actionValue P F (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F)
      (pair (IntegralBlockMomentBits.context q r.val t.val) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).entryMatrix q i j r t : ℤ) : ZMod ((characteristic P F).modulus q)) := by
  let := (characteristic P F).ring q
  let u : Fin ((characteristic P F).dimension q * (characteristic P F).rank q) := finProdFinEquiv (i, r)
  let v : Fin ((characteristic P F).dimension q * (characteristic P F).rank q) := finProdFinEquiv (j, t)
  have HP : IntegralCriticalFlatBerkowitzQuery.entryPacket (characteristic P F)
      (pair (IntegralBlockMomentBits.context q r.val t.val) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        pair q (pair (BinaryNatCode.encode u.val) (BinaryNatCode.encode v.val)) := by
    simp only [IntegralCriticalFlatBerkowitzQuery.entryPacket, original, IntegralBlockMomentBits.context,
      basisRowCode, basisColCode, MatrixMoment.EntryBits.rowIndex, MatrixMoment.EntryBits.colIndex,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  change actionValue P F (IntegralCriticalFlatMatrixQuery.writer P .actionEntry _) = _
  rw [HP]
  have HV := action_child P F g q hv u v
  have HE : IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic P F) q u v =
      (characteristic P F).entryMatrix q i j r t :=
    IntegralCoefficientBlocks.block_entry ((characteristic P F).basis q) ((characteristic P F).matrix q) i j r t
  exact HV.trans ((congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HE).trans
    (congrArg (fun m : ℕ => residueBits (((characteristic P F).entryMatrix q i j r t : ℤ) : ZMod m))
      (IntegralMixedGramCharacteristicSource.source_modulus P F q).symm))

end LeanCanny.Algebra.IntegralMixedGramUpperBits
