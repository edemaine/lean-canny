/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscFactorValue
/-! # Finite PSC factor entries retain their actual matrix under fresh queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
open scoped Classical

theorem factor_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin (powerDimension (characteristic P F) q)) :
    factorValue P F (IntegralCriticalFlatMatrixQuery.writer P p
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((characteristic P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
  let c := IntegralCriticalFlatMatrixQuery.writer P p
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) :=
    i.isLt.le.trans (IntegralMixedPscCharacteristicBits.power_cap P F g q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) :=
    j.isLt.le.trans (IntegralMixedPscCharacteristicBits.power_cap P F g q hv)
  have HS : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q := by
    apply IntegralMixedVirtualTaskBits.saved_invariance
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair]
    · simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair]
  have HC := IntegralMixedPscMatrixModel.factor_transport P F q c i.val j.val HS
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [IntegralMixedPscMatrixModel.power_snapshot] at HC
  exact HC.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin ((characteristic P F).powerMatrix q) i j))

end LeanCanny.Algebra.IntegralMixedPscUpperBits
