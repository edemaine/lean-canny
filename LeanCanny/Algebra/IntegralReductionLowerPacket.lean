/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatReductionEntry
/-! # Retained lower packets for an arbitrary actual reduction source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionLowerPacketBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
noncomputable def input (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) : List Bool :=
  IntegralCriticalFlatReductionEntryBits.lowerInput S
    (IntegralCriticalFlatReductionEntryBits.packet P S c)

noncomputable def native (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) : List Bool :=
  IntegralPurePowerReductionBits.writer S
    (IntegralCriticalFlatReductionEntryBits.packet P S c)

theorem input_parent (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) : original (input P S c) = c :=
  (IntegralCriticalFlatReductionEntryBits.lowerInput_parent _ _).trans
    (IntegralCriticalFlatReductionEntryBits.packet_parent _ _ _)

theorem input_derivative (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input P S c)) =
      PurePowerReductionBits.pivot (IntegralPurePowerReductionBits.layout S) (native P S c) := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem input_target (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input P S c)) =
      Nat.fromBitsLE (PurePowerReductionBits.differenceWord (IntegralPurePowerReductionBits.layout S) (native P S c)) := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  rfl

theorem input_row (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (basisRowCode (input P S c)) = get P .row c % S.rank c := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, IntegralPurePowerReductionBits.writer, basisRowCode,
    IntegralCriticalFlatReductionEntryBits.packet, IntegralCriticalFlatActionBits.packet,
    IntegralCriticalFlatRelativeFactorBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem input_col (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (basisColCode (input P S c)) = get P .col c % S.rank c := by
  simp only [input, IntegralCriticalFlatReductionEntryBits.lowerInput, IntegralPurePowerReductionBits.lowQuery,
    PurePowerReductionBits.sourceQuery, IntegralPurePowerReductionBits.writer, basisColCode,
    IntegralCriticalFlatReductionEntryBits.packet, IntegralCriticalFlatActionBits.packet,
    IntegralCriticalFlatRelativeFactorBits.packet, IntegralBerkowitzBlockBits.outerPacket,
    IntegralBlockMomentBits.context, original, MatrixMoment.EntryBits.colIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem native_parent (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    pairFst (PurePowerReductionBits.context (native P S c)) = c := by
  simp only [native, PurePowerReductionBits.context, IntegralPurePowerReductionBits.writer, pairFst_pair]
  exact IntegralCriticalFlatReductionEntryBits.packet_parent _ _ _

theorem input_derivative_le (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex (input P S c)) ≤ S.layout.arity c := by
  rw [input_derivative]
  have H : PurePowerReductionBits.pivot (IntegralPurePowerReductionBits.layout S) (native P S c) ≤
      (IntegralPurePowerReductionBits.layout S).arity (PurePowerReductionBits.context (native P S c)) := by
    unfold PurePowerReductionBits.pivot
    exact List.findIdx_le_length.trans_eq List.length_range
  change _ ≤ S.layout.arity (pairFst (PurePowerReductionBits.context (native P S c))) at H
  rwa [native_parent] at H

theorem difference_lt (L : PurePowerReductionBits.Layout) (p : List Bool) :
    Nat.fromBitsLE (PurePowerReductionBits.differenceWord L p) <
      count (L.arity (PurePowerReductionBits.context p)) (L.width (PurePowerReductionBits.context p)) := by
  have H := Nat.fromBitsLE_lt_pow_length (PurePowerReductionBits.differenceWord L p)
  rw [PurePowerReductionBits.differenceWord, FixedWidthNatVector.length_encode] at H
  exact H.trans_eq (by unfold count; rw [← pow_mul, Nat.mul_comm])

theorem input_target_lt (P : Parameters) (S : IntegralPurePowerActionBits.Source) (c : List Bool) :
    Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex (input P S c)) <
      count (S.layout.arity c) (S.layout.width c) := by
  rw [input_target]
  have H := difference_lt (IntegralPurePowerReductionBits.layout S) (native P S c)
  change _ < count (S.layout.arity (pairFst (PurePowerReductionBits.context (native P S c))))
    (S.layout.width (pairFst (PurePowerReductionBits.context (native P S c)))) at H
  rwa [native_parent] at H

end LeanCanny.Algebra.IntegralReductionLowerPacketBits
