/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualPowerSnapshot
public import LeanCanny.Algebra.IntegralCriticalFlatActionCorrect
/-! # Actual virtual action entries and their finite fresh children -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMatrixBits
open IntegralCriticalTotalSnapshotBits (blockMatrix integerEntry_fin)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] integerAction IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem actionEntry_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hj : get P .slot13 c = get P .slot13 q)
    (hm : modulus P c = modulus P q) (hi : get P .row c = r) (ht : get P .col c = t) :
    actionEntry P F c = residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) r t : ZMod (modulus P q)) := by
  unfold actionEntry
  rw [IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hx, hj, hi, ht]
  exact congrArg (fun m => residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) r t : ZMod m)) hm

theorem action_block_cap (P : Parameters) (F : Family) (h : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    (characteristic P F).dimension q * (characteristic P F).rank q ≤ numericCap P (RankedHistoryTask.root q) :=
  reduction_block_cap P F h q hv

attribute [local irreducible] reduction characteristic

theorem action_child (P : Parameters) (F : Family) (h : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (i j : Fin ((characteristic P F).dimension q * (characteristic P F).rank q)) :
    actionEntry P F (IntegralCriticalFlatMatrixQuery.writer P .actionEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((blockMatrix (characteristic P F) q i j : ℤ) : ZMod (modulus P q)) := by
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) := i.isLt.le.trans (action_block_cap P F h q hv)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) := j.isLt.le.trans (action_block_cap P F h q hv)
  have H := actionEntry_transport P F q
    (IntegralCriticalFlatMatrixQuery.writer P .actionEntry (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) i.val j.val
  have HE := H (by simp only [IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [HE, action_snapshot, integerEntry_fin]

theorem value19 (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (he : IntegralReductionActionBits.normalGuard (reduction P F) (IntegralCriticalFlatActionBits.packet P (reduction P F) q) →
      answer (IntegralCriticalFlatEulerBits.next P .reductionPower q) = powerValue P F q)
    (i j : Fin ((reduction P F).dimension q * (reduction P F).rank q))
    (hi : get P .row q = i.val) (hj : get P .col q = j.val) :
    (IntegralCriticalFlatActionBits.program P (reduction P F)).value answer q = actionEntry P F q := by
  let := (reduction P F).ring q
  have HD : (reduction P F).dimension q * (reduction P F).rank q =
      (characteristic P F).dimension q * (characteristic P F).rank q := by unfold characteristic; rfl
  let r := Fin.cast HD i
  let t := Fin.cast HD j
  have HE := IntegralCriticalFlatActionBits.value_block P (reduction P F) answer q he i j hi hj
  have HM : (reduction P F).modulus q = modulus P q := by unfold reduction relative; rfl
  have HEM := HE.trans (congrArg (fun m => residueBits ((IntegralCoefficientBlocks.blockHom ((reduction P F).basis q)
    ((reduction P F).dimension q) ((reduction P F).actionMatrix q) i j : ℤ) : ZMod m)) HM)
  have HB : IntegralCoefficientBlocks.blockHom ((reduction P F).basis q) ((reduction P F).dimension q)
      ((reduction P F).actionMatrix q) i j = blockMatrix (characteristic P F) q r t := by unfold characteristic; rfl
  rw [HB] at HEM
  have HF : IntegralCriticalTotalSnapshotBits.integerEntry (blockMatrix (characteristic P F) q) i.val j.val =
      blockMatrix (characteristic P F) q r t := integerEntry_fin _ r t
  rw [actionEntry, hi, hj, action_snapshot, HF]
  exact HEM

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
