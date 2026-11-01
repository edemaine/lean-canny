/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualReductionEntry
public import LeanCanny.Algebra.IntegralCriticalActualLowerEntry
/-! # Actual lower-reader packets and their bounded native selectors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualLowerChildBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem low_snapshot (F : Scripts) (h : Controls F) (p : List Bool) :
    (relativeAccess F h).low p = IntegralCriticalActualLowerEntry.lowerEntryAt
      (IntegralCriticalTotalCreatingBits.atFamily F (original p))
      (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))
      (Nat.fromBitsLE (basisRowCode p)) (Nat.fromBitsLE (basisColCode p))
      (IntegralCriticalHistoryTask.modulus F.toParameters (original p))
      (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters (original p)) := rfl

attribute [local irreducible] relative relativeAccess

noncomputable def input (F : Scripts) (c : List Bool) : List Bool :=
  IntegralCriticalFlatReductionEntryBits.lowerInput (relative F)
    (IntegralCriticalFlatReductionEntryBits.packet F.toParameters (relative F) c)

noncomputable def native (F : Scripts) (c : List Bool) : List Bool :=
  IntegralPurePowerReductionBits.writer (relative F)
    (IntegralCriticalFlatReductionEntryBits.packet F.toParameters (relative F) c)

theorem input_parent (F : Scripts) (c : List Bool) : original (input F c) = c :=
  (IntegralCriticalFlatReductionEntryBits.lowerInput_parent _ _).trans
    (IntegralCriticalFlatReductionEntryBits.packet_parent _ _ _)

theorem input_derivative (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input F c)) =
      PurePowerReductionBits.pivot (IntegralPurePowerReductionBits.layout (relative F)) (native F c) := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem input_target (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input F c)) =
      Nat.fromBitsLE (PurePowerReductionBits.differenceWord (IntegralPurePowerReductionBits.layout (relative F)) (native F c)) := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  rfl

theorem input_row (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (basisRowCode (input F c)) = get F.toParameters .row c % (relative F).rank c := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, IntegralPurePowerReductionBits.writer, basisRowCode,
    IntegralCriticalFlatReductionEntryBits.packet, IntegralCriticalFlatActionBits.packet,
    IntegralCriticalFlatRelativeFactorBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem input_col (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (basisColCode (input F c)) = get F.toParameters .col c % (relative F).rank c := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, IntegralPurePowerReductionBits.writer, basisColCode,
    IntegralCriticalFlatReductionEntryBits.packet, IntegralCriticalFlatActionBits.packet,
    IntegralCriticalFlatRelativeFactorBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem native_parent (F : Scripts) (c : List Bool) :
    pairFst (PurePowerReductionBits.context (native F c)) = c := by
  simp only [native, PurePowerReductionBits.context, IntegralPurePowerReductionBits.writer, pairFst_pair]
  exact IntegralCriticalFlatReductionEntryBits.packet_parent _ _ _

theorem input_derivative_le (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input F c)) ≤ (relative F).layout.arity c := by
  rw [input_derivative]
  have H : PurePowerReductionBits.pivot (IntegralPurePowerReductionBits.layout (relative F)) (native F c) ≤
      (IntegralPurePowerReductionBits.layout (relative F)).arity (PurePowerReductionBits.context (native F c)) := by
    unfold PurePowerReductionBits.pivot
    exact List.findIdx_le_length.trans_eq List.length_range
  change _ ≤ (relative F).layout.arity (pairFst (PurePowerReductionBits.context (native F c))) at H
  rwa [native_parent] at H

theorem difference_lt (L : PurePowerReductionBits.Layout) (p : List Bool) :
    Nat.fromBitsLE (PurePowerReductionBits.differenceWord L p) <
      count (L.arity (PurePowerReductionBits.context p)) (L.width (PurePowerReductionBits.context p)) := by
  have H := Nat.fromBitsLE_lt_pow_length (PurePowerReductionBits.differenceWord L p)
  rw [PurePowerReductionBits.differenceWord, FixedWidthNatVector.length_encode] at H
  exact H.trans_eq (by unfold count; rw [← pow_mul, Nat.mul_comm])

theorem input_target_lt (F : Scripts) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input F c)) <
      count ((relative F).layout.arity c) ((relative F).layout.width c) := by
  rw [input_target]
  have H := difference_lt (IntegralPurePowerReductionBits.layout (relative F)) (native F c)
  change _ < count ((relative F).layout.arity (pairFst (PurePowerReductionBits.context (native F c))))
    ((relative F).layout.width (pairFst (PurePowerReductionBits.context (native F c)))) at H
  rwa [native_parent] at H

end LeanCanny.Algebra.IntegralCriticalFlatActualLowerChildBits
