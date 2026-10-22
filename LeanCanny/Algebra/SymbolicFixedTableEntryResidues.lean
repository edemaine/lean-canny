/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableProgram
public import LeanCanny.Algebra.BerkowitzTaskResidues

/-! # Modulus bounds for every symbolic source entry, including malformed queries -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial MatrixPower SymbolicScaledSquarefree

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.succ
  BinaryNat.div BinaryNat.mod BinaryNat.mul
  SylvesterPolynomialBits.RecursiveStage.active SylvesterPolynomialBits.RecursiveStage.selectRight
  SylvesterPolynomialBits.RecursiveStage.rightInput SylvesterPolynomialBits.RecursiveStage.leftInput

theorem coefficient_length_le (P : List Bool → Polynomial Coefficient) (q : List Bool) :
    (coefficient P q).length ≤ (Nat.fromBitsLE (pairSnd (pairFst q)) + 1).size := by
  let : NeZero (Nat.fromBitsLE (pairSnd (pairFst q)) + 1) := ⟨by omega⟩
  exact residueBits_length_le _ _

theorem Family.sliced_entry_length_le (F : Family) (p : List Bool) :
    (F.access.modular.determinant.entry p).length ≤ (CannyResultantBits.mValue (pairFst p)).size := by
  change (F.access.modular.bits.entry p).length ≤ _
  rw [SylvesterPolynomialBits.RecursiveStage.entry_eq]
  split_ifs
  · change (F.access.constantCoefficient (SylvesterPolynomialBits.RecursiveStage.rightInput p)).length ≤ _
    unfold CannyResultantBits.Access.constantCoefficient
    split_ifs
    · have hb := coefficient_length_le F.right (sliceCoefficientQuery
        (pair (pairFst (SylvesterPolynomialBits.RecursiveStage.rightInput p))
          (ShiftCoefficientBits.leftIndex (SylvesterPolynomialBits.RecursiveStage.rightInput p))))
      simpa only [Family.access, Function.comp_apply, sliceCoefficientQuery, pairFst_pair, pairSnd_pair,
        SylvesterPolynomialBits.RecursiveStage.rightInput_context, CannyResultantBits.mValue] using hb
    · exact Nat.zero_le _
  · change (F.sliced.shiftSource.value (SylvesterPolynomialBits.RecursiveStage.leftInput F.access.modular.bits p)).length ≤ _
    have hm : ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput F.access.modular.bits p) =
        CannyResultantBits.mValue (pairFst p) := by
      simp only [ShiftCoefficientBits.mValue, ShiftCoefficientBits.modulusMinusOne,
        SylvesterPolynomialBits.RecursiveStage.leftInput_context, CannyResultantBits.mValue]
    have hb : (F.sliced.shiftSource.value (SylvesterPolynomialBits.RecursiveStage.leftInput F.access.modular.bits p)).length ≤
        (ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput F.access.modular.bits p)).size := by
      let : NeZero (ShiftCoefficientBits.mValue (SylvesterPolynomialBits.RecursiveStage.leftInput F.access.modular.bits p)) :=
        ⟨by unfold ShiftCoefficientBits.mValue; omega⟩
      exact residueBits_length_le _ _
    exact hm ▸ hb
  · exact Nat.zero_le _

theorem Family.entry_length_le (F : Family) (q : List Bool) :
    (F.entry q).length ≤ (Nat.fromBitsLE (pairSnd (pairFst q)) + 1).size := by
  have h := F.sliced_entry_length_le (entryQuery q)
  simpa only [Family.entry, Function.comp_apply, entryQuery, CannyResultantBits.mValue, pairFst_pair, pairSnd_pair] using h

theorem Family.encodedEntry_length_le (F : Family) (radix : List Bool → List Bool) (q : List Bool) :
    (F.encodedEntry radix q).length ≤ (Nat.fromBitsLE (pairSnd (pairFst q)) + 1).size := by
  have h := F.entry_length_le (splitInput radix q)
  simpa only [Family.encodedEntry, Function.comp_apply, splitInput, pairFst_pair, pairSnd_pair] using h

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
