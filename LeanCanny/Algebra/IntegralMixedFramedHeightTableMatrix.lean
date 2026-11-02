/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightBankSnapshot
public import LeanCanny.Algebra.IntegralMixedHeightTableQueryBounds
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableRead
/-! # Collected height words are the literal old-bank multiplication entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightTableMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits (bankFamily state oldRank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def matrix (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) (i : ℕ) :=
  IntegralMixedFramedOldHeightBankBits.sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P q) i
    (IntegralMixedHeightTableQueryBits.oldRow P q) (IntegralMixedHeightTableQueryBits.oldCol P q)

theorem query_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedFramedOldHeightBits.value P D J (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))) =
      residueBits (matrix P D J q i : ZMod (modulus P q)) := by
  let c := IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))
  have H := IntegralMixedFramedOldHeightBankBits.value_source P D J c
  have HI : IntegralMixedFramedOldHeightBankBits.sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P c)
      (get P .sourceIndex c) (get P .row c) (get P .col c) = matrix P D J q i := by
    rw [IntegralMixedHeightTableQueryBits.writer_index P q i hi,
      IntegralMixedHeightTableQueryBits.writer_row, IntegralMixedHeightTableQueryBits.writer_col]
    exact IntegralMixedFramedOldHeightBankBits.sourceEntry_invariance P D J q c
      (IntegralMixedHeightTableQueryBits.writer_root P q i) (IntegralMixedHeightTableQueryBits.writer_birth P q i) _ _ _
  have HM : modulus P c = modulus P q := IntegralMixedHeightTableQueryBits.writer_modulus P q i
  exact H.trans (congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HI HM)

noncomputable def row (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Fin (oldRank P D J q) :=
  ⟨IntegralMixedHeightTableQueryBits.oldRow P q,
    (IntegralMixedHeightTableQueryBits.oldRow_lt P q).trans_eq (IntegralMixedFramedOldHeightBits.oldRank_eq P D J q).symm⟩
noncomputable def col (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Fin (oldRank P D J q) :=
  ⟨IntegralMixedHeightTableQueryBits.oldCol P q,
    (IntegralMixedHeightTableQueryBits.oldCol_lt P q).trans_eq (IntegralMixedFramedOldHeightBits.oldRank_eq P D J q).symm⟩

theorem matrix_entry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))) :
    matrix P D J q i.val = Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
      (IntegralMixedHistory.cleared (state P D J q) i) (row P D J q) (col P D J q) := by
  have HV : i.val < (bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q) ∧
      IntegralMixedHeightTableQueryBits.oldRow P q < oldRank P D J q ∧
      IntegralMixedHeightTableQueryBits.oldCol P q < oldRank P D J q := ⟨i.isLt, (row P D J q).isLt, (col P D J q).isLt⟩
  unfold matrix IntegralMixedFramedOldHeightBankBits.sourceEntry
  split_ifs with HC
  · rfl
  · exact False.elim (HC HV)

theorem entryWord_height (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedFramedHeightTablePassBits.entryWord P D J q (birth P q + i) = residueBits (matrix P D J q i : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedHeightTablePassBits.entryWord, dite_eq_right (by omega), show birth P q + i - birth P q = i by omega]
  exact query_value P D J q i hi

theorem number_height (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedFramedHeightTableReadBits.number P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) (birth P q + i) =
      (matrix P D J q i : ZMod (modulus P q)).val := by
  rw [IntegralMixedFramedHeightTableReadBits.number_value P D J q _ (by unfold IntegralMixedFramedHeightTablePassBits.count; omega)]
  change Nat.fromBitsLE (IntegralMixedFramedHeightTablePassBits.entryWord P D J q (birth P q + i)) = _
  rw [entryWord_height P D J q i hi]
  exact Nat.fromBitsLE_bits _

end LeanCanny.Algebra.IntegralMixedFramedHeightTableMatrixBits
