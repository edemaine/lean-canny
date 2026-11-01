/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationSnapshots
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStageLocal
/-! # Actual relative-factor entries under finite mixed queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open IntegralCriticalTotalSnapshotBits (integerEntry_fin)
set_option backward.isDefEq.respectTransparency false
noncomputable def factorValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q) (get P .row q) (get P .col q) : ZMod (modulus P q))

attribute [local irreducible] integerPower IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem factorValue_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q)
    (hm : modulus P c = modulus P q) (hi : get P .row c = r) (ht : get P .col c = t) :
    factorValue P F c = residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
      r t : ZMod (modulus P q)) := by
  unfold factorValue
  rw [IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hi, ht]
  exact congrArg (fun m => residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
    r t : ZMod m)) hm

theorem factor_child (P : Parameters) (F : Family) (h : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin (IntegralBerkowitzBlockBits.powerDimension (source P F) q)) :
    factorValue P F (IntegralCriticalFlatMatrixQuery.writer P p
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((source P F).powerMatrix q i j : ℤ) : ZMod (modulus P q)) := by
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) := i.isLt.le.trans (factor_cap P F h q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) := j.isLt.le.trans (factor_cap P F h q hv)
  have H := factorValue_transport P F q
    (IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) i.val j.val
  have HE := H (by simp only [IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [HE, power_snapshot, integerEntry_fin]

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
