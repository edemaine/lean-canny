/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFamily
public import LeanCanny.Algebra.IntegralMixedAffineCoefficients
public import LeanCanny.Algebra.IntegralMixedHeightCells
/-! # Literal creating-source scalar cells are keyed by the saved birth

The instruction, spatial source and original rule come from the same saved
prefix key. No source body is pulled back through a root-only projection.
These definitions supply no cost assertion for an interpreted state.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedScalarCellsBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev physicalFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedPhysicalBits.family P D H
noncomputable abbrev virtualFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H

noncomputable def rule (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    CriticalRule (P.ambient (pairFst key)) :=
  if IntegralMixedHeightCellsBits.context key = 1 then (physicalFamily P D H).rule key else ((virtualFamily P D H).rule key).critical

noncomputable def affine (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : AffineExpr :=
  let key := IntegralMixedVirtualTaskBits.saved P q
  if hi : get P .slot8 q < P.ambient (pairFst key) + 1 then (rule P D H key).heights ⟨get P .slot8 q, hi⟩ else .constant 0

noncomputable def leading (P : Parameters) (D : Plan P) (q : List Bool) : ℤ :=
  (IntegralMixedFramedHistoryFamilyBits.instruction P D (IntegralMixedVirtualTaskBits.saved P q)).source.leading
noncomputable def leadingValue (P : Parameters) (D : Plan P) (q : List Bool) := residueBits (leading P D q : ZMod (modulus P q))

noncomputable def cell (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (tag i : ℕ) : ℤ :=
  let key := IntegralMixedVirtualTaskBits.saved P q
  if tag = 0 then IntegralMixedAffineCoefficients.constantCoefficient (affine P D H q) else
  if tag = 1 then IntegralMixedAffineCoefficients.referenceCoefficient (affine P D H q) i else
  if tag = 2 then
    if hi : i < P.ambient (pairFst key) + 1 then (rule P D H key).scales ⟨i, hi⟩ else 1
  else if tag = 3 then
    if get P .slot8 q = ((virtualFamily P D H).rule key).height.val then ((virtualFamily P D H).rule key).slope else 0
  else 0
noncomputable def reader (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  residueBits (cell P D H (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z)))
    (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))
abbrev Primitive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) := SpaceFunction (reader P D H)
abbrev LeadingPrimitive (P : Parameters) (D : Plan P) := SpaceFunction (leadingValue P D)

theorem rule_physical (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hx : get P .slot15 q = 1) : rule P D H (IntegralMixedVirtualTaskBits.saved P q) =
      (physicalFamily P D H).rule (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [rule, IntegralMixedHeightCellsBits.context_saved, ite_eq_left hx]

theorem rule_virtual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hx : get P .slot15 q ≠ 1) : rule P D H (IntegralMixedVirtualTaskBits.saved P q) =
      ((virtualFamily P D H).rule (IntegralMixedVirtualTaskBits.saved P q)).critical := by
  rw [rule, IntegralMixedHeightCellsBits.context_saved, ite_eq_right hx]

theorem leading_key (P : Parameters) (D : Plan P) (q : List Bool) : leading P D q =
    (IntegralMixedFramedHistoryFamilyBits.instruction P D (IntegralMixedVirtualTaskBits.saved P q)).source.leading := rfl

theorem reader_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (tag i : ℕ) : reader P D H (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))) =
      residueBits (cell P D H q tag i : ZMod (modulus P q)) := by
  unfold reader
  have HC : cell P D H (pairFst (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))))
      (Nat.fromBitsLE (pairFst (pairSnd (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))))))
      (Nat.fromBitsLE (pairSnd (pairSnd (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i)))))) = cell P D H q tag i := by
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HC
    (congrArg (modulus P) (pairFst_pair _ _))
end LeanCanny.Algebra.IntegralMixedFramedScalarCellsBits
