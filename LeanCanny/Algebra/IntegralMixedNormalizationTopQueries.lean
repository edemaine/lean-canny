/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationTopSource
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Fresh native entries for the actual normalization matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry (top F (IntegralMixedVirtualTaskBits.saved P q))
    (get P .row q) (get P .col q) : ZMod (modulus P q))

def entryTask (P : Parameters) (p : Phase) (z : List Bool) : List Bool :=
  IntegralCriticalFlatMatrixQuery.writer P p (pair (original z)
    (pair (MatrixMoment.EntryBits.rowIndex z) (MatrixMoment.EntryBits.colIndex z)))

theorem entryTask_FP (P : Parameters) (a : Access P) (p : Phase) : entryTask P p ∈ FP :=
  mem_FP_comp (mem_FP_pair original_FP
    (mem_FP_pair MatrixMoment.EntryBits.rowIndex_mem_FP MatrixMoment.EntryBits.colIndex_mem_FP))
    (IntegralCriticalFlatMatrixQuery.writer_FP P a p)

theorem value_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hi : get P .row c = r) (ht : get P .col c = t) :
    value P F c = residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (top F (IntegralMixedVirtualTaskBits.saved P q)) r t : ZMod (modulus P q)) := by
  unfold value
  rw [IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hm, hi, ht]

theorem child_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((source P F).dimension q)) :
    value P F (IntegralCriticalFlatMatrixQuery.writer P p
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((top F (IntegralMixedVirtualTaskBits.saved P q) i j : ℤ) : ZMod (modulus P q)) := by
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) := i.isLt.le.trans (dimension_cap P F g q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) := j.isLt.le.trans (dimension_cap P F g q hv)
  have H := value_transport P F q
    (IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) i.val j.val
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]; exact min_eq_left HJ)
  exact H.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ i j))

theorem entryTask_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((source P F).dimension q)) (r t : Fin 1) :
    value P F (entryTask P p (pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((source P F).entryMatrix q i j r t : ℤ) : ZMod (modulus P q)) := by
  simp only [entryTask, original, IntegralBlockMomentBits.context, MatrixMoment.EntryBits.rowIndex,
    MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair]
  exact (child_value P F g p q hv i j).trans
    (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (singleton_entry _ r t).symm)

theorem entryTask_frame (P : Parameters) (p : Phase) (z : List Bool) (hp : p.code < phase (original z)) :
    IntegralMixedRoutineTaskBits.Frame P (original z) (entryTask P p z) := by
  have H := IntegralMixedMatrixFrames.matrix_frame P p
    (pair (original z) (pair (MatrixMoment.EntryBits.rowIndex z) (MatrixMoment.EntryBits.colIndex z)))
    (by simpa only [pairFst_pair] using hp)
  unfold entryTask
  simpa only [pairFst_pair] using H

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
