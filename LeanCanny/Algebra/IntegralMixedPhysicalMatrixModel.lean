/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperSources
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
/-! # Natural-index matrix models for the selected physical source

Integer matrix data depend only on the saved parent and selected coordinate.
Fresh output fields, routine tags, and modulus do not select another matrix.
Natural indices give zero outside the actual finite matrix.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralCriticalTotalSnapshotBits
set_option backward.isDefEq.respectTransparency false

noncomputable def core (F : Family) (key : List Bool) (j : ℕ) :=
  IntegralMixedPhysicalSnapshotBits.sourceAt F key j 0 0 0 0 1 (by decide)
noncomputable def relativeAt (F : Family) (key : List Bool) (j : ℕ) := IntegralClearedCriticalBits.relativeSource (core F key j)
noncomputable def reductionAt (F : Family) (key : List Bool) (j : ℕ) := IntegralPurePowerActionBits.reductionSource (relativeAt F key j)
noncomputable def actionAt (F : Family) (key : List Bool) (j : ℕ) := IntegralReductionActionBits.actionSource (reductionAt F key j)

noncomputable def integerReduction (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (reductionAt F key j).toSource []) r t
noncomputable def integerAction (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (actionAt F key j) []) r t
noncomputable def integerPower (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  integerEntry ((actionAt F key j).powerMatrix []) r t

theorem reduction_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerReduction F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q) r t =
      integerEntry (blockMatrix (IntegralMixedPhysicalUpperBits.reduction P F).toSource q) r t := rfl
theorem action_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerAction F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q) r t =
      integerEntry (blockMatrix (IntegralMixedPhysicalUpperBits.characteristic P F) q) r t := rfl
theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerPower F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q) r t =
      integerEntry ((IntegralMixedPhysicalUpperBits.characteristic P F).powerMatrix q) r t := rfl

noncomputable def reductionEntry (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerReduction F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))
noncomputable def actionEntry (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerAction F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))
noncomputable def relativeFactor (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerPower F (IntegralMixedPhysicalTaskBits.saved P q) (get P .slot13 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))

attribute [local irreducible] integerReduction integerAction integerPower
  IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem reductionEntry_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) (hj : get P .slot13 c = get P .slot13 q)
    (hm : modulus P c = modulus P q) (hi : get P .row c = r) (ht : get P .col c = t) :
    reductionEntry P F c = residueBits (integerReduction F (IntegralMixedPhysicalTaskBits.saved P q)
      (get P .slot13 q) r t : ZMod (modulus P q)) := by
  unfold reductionEntry
  rw [IntegralMixedPhysicalTaskBits.saved_invariance P q c hr hb hx, hj, hi, ht]
  exact congrArg (fun m => residueBits (integerReduction F (IntegralMixedPhysicalTaskBits.saved P q)
    (get P .slot13 q) r t : ZMod m)) hm

theorem reduction_block_cap (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool) :
    (IntegralMixedPhysicalUpperBits.reduction P F).dimension q * (IntegralMixedPhysicalUpperBits.reduction P F).rank q ≤
      numericCap P (RankedHistoryTask.root q) := by
  have HC : PurePowerReductionBounds.dimension (P.ambient (RankedHistoryTask.root q) + 1)
      (P.degree (RankedHistoryTask.root q)) * rankCap P (RankedHistoryTask.root q) ≤
        numericCap P (RankedHistoryTask.root q) := by
    unfold numericCap
    exact IntegralCriticalQueryBounds.action_block_le _ _ _ _ _ _ _ _
  exact (Nat.mul_le_mul (IntegralMixedPhysicalCaps.dimension_le P F h q)
    (IntegralMixedPhysicalCaps.rank_le P F h q)).trans HC

attribute [local irreducible] IntegralMixedPhysicalUpperBits.reduction

theorem reduction_child (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool)
    (i j : Fin ((IntegralMixedPhysicalUpperBits.reduction P F).dimension q * (IntegralMixedPhysicalUpperBits.reduction P F).rank q)) :
    reductionEntry P F (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((blockMatrix (IntegralMixedPhysicalUpperBits.reduction P F).toSource q i j : ℤ) : ZMod (modulus P q)) := by
  have HI : i.val ≤ numericCap P (RankedHistoryTask.root q) := i.isLt.le.trans (reduction_block_cap P F h q)
  have HJ : j.val ≤ numericCap P (RankedHistoryTask.root q) := j.isLt.le.trans (reduction_block_cap P F h q)
  have H := reductionEntry_transport P F q
    (IntegralCriticalFlatMatrixQuery.writer P .reductionEntry (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) i.val j.val
  have HE := H (by simp only [IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, reduceCtorEq, ite_false, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair])
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]; exact min_eq_left HI)
    (by simp only [IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]; exact min_eq_left HJ)
  rw [HE, reduction_snapshot, integerEntry_fin]

end LeanCanny.Algebra.IntegralMixedPhysicalMatrixBits
