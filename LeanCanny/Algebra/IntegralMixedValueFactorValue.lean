/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueFactorTasks
/-! # Exact reflected Gram output over the saved relative parent -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueFactorValue
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueFactorTasks
open scoped Classical
attribute [local irreducible] residueBits IntegralMixedValueDoubleNilpotent.basis
attribute [local irreducible] IntegralMixedCutNilpotent.value IntegralMixedCutNilpotent.basis
attribute [local irreducible] IntegralMixedValueCharacteristicExtraction.integerValue

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix
    (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
    (IntegralMixedCutNilpotent.value ((IntegralMixedVirtualTaskBits.family P F).state q)
      ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
      (.value ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (choice P F q)))
    ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q) : ℤ) :
      ZMod (modulus P q))

theorem value_length (P : Parameters) (F : Family) (q : List Bool) [NeZero (modulus P q)] :
    (value P F q).length ≤ (modulus P q).size := residueBits_length_le _ _

theorem child_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hk : 0 < (choice P F q).val) :
    IntegralMixedGramUpperBits.characteristicValue P F (query P F q) = value P F q := by
  rw [IntegralMixedValueCharacteristicExtraction.characteristic_snapshot, query_saved]
  simp only [query_get P F g q hv, reduceCtorEq, ite_false, ite_true]
  have HM := congrArg (fun m : ℕ => residueBits
    (IntegralMixedValueCharacteristicExtraction.integerValue F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (selectedRow P F q) (selectedCol P F q) : ZMod m)) (query_modulus P F q)
  apply HM.trans
  have H := IntegralMixedValueCharacteristicExtraction.integerValue_selected_integer
    (IntegralMixedVirtualTaskBits.family P F) (get P .slot13 q)
    (IntegralMixedVirtualTaskBits.indices P F).row (IntegralMixedVirtualTaskBits.indices P F).col
    (modulus P) (modulus_ne_zero P) (choice P F) q hk
  let I := IntegralMixedValueCharacteristicExtraction.selectedIndices (IntegralMixedVirtualTaskBits.family P F)
    (get P .slot13 q) (IntegralMixedVirtualTaskBits.indices P F).row (IntegralMixedVirtualTaskBits.indices P F).col
    (modulus P) (modulus_ne_zero P)
  have HR : (IntegralMixedValueDeterminantSource.row (IntegralMixedVirtualTaskBits.family P F) I (choice P F) q).val =
      selectedRow P F q := by
    simp only [IntegralMixedValueDeterminantSource.row, IntegralMixedCutNilpotent.pairIndex_value,
      selectedRow, IntegralMixedValueCharacteristicExtraction.selectedIndices, I]
  have HT : (IntegralMixedValueDeterminantSource.col (IntegralMixedVirtualTaskBits.family P F) I q).val =
      selectedCol P F q := by
    simp only [IntegralMixedValueDeterminantSource.col, IntegralMixedCutNilpotent.pairIndex_value,
      selectedCol, IntegralMixedValueCharacteristicExtraction.selectedIndices, I]
  have HC : (IntegralMixedValueHomogeneousSnapshot.pointIndices (IntegralMixedVirtualTaskBits.family P F)
      (get P .slot13 q)).coordinate q = (IntegralMixedVirtualTaskBits.indices P F).coordinate q := rfl
  rw [IntegralMixedValueCharacteristicExtraction.integerValue_pull, HR, HT, HC] at H
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) H

theorem value_zero (P : Parameters) (F : Family) (q : List Bool) (hk : (choice P F q).val = 0) :
    value P F q = [] := by
  have HE : choice P F q = 0 := Fin.ext hk
  have HZ := IntegralMixedValueMatrixSource.nilpotent_value_zero
    ((IntegralMixedVirtualTaskBits.family P F).state q) ((IntegralMixedVirtualTaskBits.family P F).birth_bound q)
    ((IntegralMixedVirtualTaskBits.family P F).rule q) ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)
  let read (z : IntegralMixedValueDoubleNilpotent.First ((IntegralMixedVirtualTaskBits.family P F).state q)) : List Bool :=
    residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis z
      ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q) : ℤ) : ZMod (modulus P q))
  change read _ = []
  rw [HE]
  exact (congrArg read HZ).trans (by
    simp only [read, map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])

noncomputable def packet (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  pair (pair (IntegralMixedVirtualTaskBits.saved P q) (BinaryNatCode.encode (modulus P q - 1)))
    (pair (BinaryNatCode.encode ((IntegralMixedVirtualTaskBits.indices P F).row q).val)
      (BinaryNatCode.encode ((IntegralMixedVirtualTaskBits.indices P F).col q).val))

theorem value_packet (P : Parameters) (F : Family) (q : List Bool)
    (hkind : F.kind (IntegralMixedVirtualTaskBits.saved P q) =
      .value ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (choice P F q)) :
    value P F q = IntegralMixedCutQueries.value F (packet P F q) := by
  let z : ℤ := Algebra.leftMulMatrix
    (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
    (IntegralMixedCutNilpotent.value ((IntegralMixedVirtualTaskBits.family P F).state q)
      ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
      (.value ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (choice P F q)))
    ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q)
  have H := IntegralMixedCutQueries.value_packet F (IntegralMixedVirtualTaskBits.saved P q)
    (BinaryNatCode.encode (modulus P q - 1))
    ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q)
  rw [hkind] at H
  have HM : Nat.fromBitsLE (BinaryNatCode.encode (modulus P q - 1)) + 1 = modulus P q := by
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P q))
  change residueBits (z : ZMod (modulus P q)) = _
  exact (congrArg (fun m : ℕ => residueBits (z : ZMod m)) HM).symm.trans H.symm

end LeanCanny.Algebra.IntegralMixedValueFactorValue
