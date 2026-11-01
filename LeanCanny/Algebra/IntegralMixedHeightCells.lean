/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPhysicalBridge
public import LeanCanny.Algebra.IntegralMixedAffineCoefficients
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Algebra.IntegralMixedHeightTablePass
/-! # Literal original affine and scale cells for mixed scalar heights

These are immutable creating-rule cells. A charged reader for them supplies
no old-state, common-denominator, height, or producer-leading evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightCellsBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (key : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd key))

noncomputable def physicalFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) :=
  IntegralMixedFullPhysicalBits.family P (IntegralMixedFullHistoryFamilyBits.physicalData P D)

noncomputable def rule (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) : CriticalRule (P.ambient (pairFst key)) :=
  if context key = 1 then (physicalFamily P D).rule key else ((IntegralMixedFullHistoryFamilyBits.family P D).rule key).critical

noncomputable def affine (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : AffineExpr :=
  let key := IntegralMixedVirtualTaskBits.saved P q
  if hi : get P .slot8 q < P.ambient (pairFst key) + 1 then (rule P D key).heights ⟨get P .slot8 q, hi⟩ else .constant 0

noncomputable def cell (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (tag i : ℕ) : ℤ :=
  let key := IntegralMixedVirtualTaskBits.saved P q
  if tag = 0 then IntegralMixedAffineCoefficients.constantCoefficient (affine P D q) else
  if tag = 1 then IntegralMixedAffineCoefficients.referenceCoefficient (affine P D q) i else
  if tag = 2 then
    if hi : i < P.ambient (pairFst key) + 1 then (rule P D key).scales ⟨i, hi⟩ else 1
  else if tag = 3 then
    if get P .slot8 q = ((IntegralMixedFullHistoryFamilyBits.family P D).rule key).height.val then
      ((IntegralMixedFullHistoryFamilyBits.family P D).rule key).slope else 0
  else 0

noncomputable def reader (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  residueBits (cell P D (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z)))
    (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))

abbrev Primitive (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := SpaceFunction (reader P D)

def query (tag : ℕ) (p : List Bool) := pair (pairFst p) (pair (BinaryNatCode.encode tag) (pairSnd p))
theorem query_FP (tag : ℕ) : query tag ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (constFn_mem_FP _) pairSnd_mem_FP)

attribute [local irreducible] cell affine modulus

theorem reader_packet (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (tag i : ℕ) :
    reader P D (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))) =
      residueBits (cell P D q tag i : ZMod (modulus P q)) := by
  unfold reader
  have HC : cell P D (pairFst (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))))
      (Nat.fromBitsLE (pairFst (pairSnd (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i))))))
      (Nat.fromBitsLE (pairSnd (pairSnd (pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i)))))) = cell P D q tag i := by
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HM := congrArg (modulus P) (pairFst_pair q (pair (BinaryNatCode.encode tag) (BinaryNatCode.encode i)))
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HC HM

theorem context_saved (P : Parameters) (q : List Bool) : context (IntegralMixedVirtualTaskBits.saved P q) = get P .slot15 q := by
  simp only [context, IntegralMixedVirtualTaskBits.saved, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem rule_physical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hx : get P .slot15 q = 1) :
    rule P D (IntegralMixedVirtualTaskBits.saved P q) = (physicalFamily P D).rule (IntegralMixedVirtualTaskBits.saved P q) := by
  rw [rule, context_saved, ite_eq_left hx]

theorem rule_virtual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hx : get P .slot15 q ≠ 1) :
    rule P D (IntegralMixedVirtualTaskBits.saved P q) =
      ((IntegralMixedFullHistoryFamilyBits.family P D).rule (IntegralMixedVirtualTaskBits.saved P q)).critical := by
  rw [rule, context_saved, ite_eq_right hx]

end LeanCanny.Algebra.IntegralMixedHeightCellsBits
