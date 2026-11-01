/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperSelection
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStageLocal
/-! # Actual relative-factor entries under finite mixed queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedGramMatrixModel
open IntegralCriticalTotalSnapshotBits (integerEntry_fin)
attribute [local irreducible] integerPower IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem relativeFactor_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hj : get P .slot13 c = get P .slot13 q)
    (hm : modulus P c = modulus P q) (hi : get P .row c = r) (ht : get P .col c = t) :
    factorValue P F c = residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) r t : ZMod (modulus P q)) := by
  unfold factorValue
  rw [IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hj, hi, ht]
  exact congrArg (fun m => residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) r t : ZMod m)) hm

theorem factor_block_cap (P : Parameters) (F : Family) (h : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralBerkowitzBlockBits.powerDimension (characteristic P F) q ≤ numericCap P (RankedHistoryTask.root q) :=
  IntegralMixedGramCharacteristicBounds.power_cap P F h q hv

attribute [local irreducible] IntegralMixedGramCharacteristicSource.source

theorem relativeFactor_child (P : Parameters) (F : Family) (h : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin (IntegralBerkowitzBlockBits.powerDimension (characteristic P F) q)) :
    factorValue P F (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) := i.isLt.le.trans (factor_block_cap P F h q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) := j.isLt.le.trans (factor_block_cap P F h q hv)
  have H := relativeFactor_transport P F q
    (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) i.val j.val
  have HE := H (by simp only [IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [HE, IntegralMixedGramMatrixModel.power_snapshot]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (integerEntry_fin ((characteristic P F).powerMatrix q) i j)

end LeanCanny.Algebra.IntegralMixedGramUpperBits
