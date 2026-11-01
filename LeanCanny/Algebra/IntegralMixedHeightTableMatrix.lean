/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightBankSnapshot
public import LeanCanny.Algebra.IntegralMixedHeightTableQueryBounds
public import LeanCanny.Algebra.IntegralMixedHeightTableRead
/-! # Collected height words are the literal old-bank multiplication entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTableMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits (bankFamily state oldRank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def matrix (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :=
  IntegralMixedOldHeightBankBits.sourceEntry P D (IntegralMixedVirtualTaskBits.saved P q) i
    (IntegralMixedHeightTableQueryBits.oldRow P q) (IntegralMixedHeightTableQueryBits.oldCol P q)

theorem query_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedOldHeightBits.value P D (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))) =
      residueBits (matrix P D q i : ZMod (modulus P q)) := by
  let c := IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))
  have H := IntegralMixedOldHeightBankBits.value_source P D c
  have HI : IntegralMixedOldHeightBankBits.sourceEntry P D (IntegralMixedVirtualTaskBits.saved P c)
      (get P .sourceIndex c) (get P .row c) (get P .col c) = matrix P D q i := by
    rw [IntegralMixedHeightTableQueryBits.writer_index P q i hi,
      IntegralMixedHeightTableQueryBits.writer_row, IntegralMixedHeightTableQueryBits.writer_col]
    exact IntegralMixedOldHeightBankBits.sourceEntry_invariance P D q c
      (IntegralMixedHeightTableQueryBits.writer_root P q i) (IntegralMixedHeightTableQueryBits.writer_birth P q i) _ _ _
  have HM : modulus P c = modulus P q := IntegralMixedHeightTableQueryBits.writer_modulus P q i
  exact H.trans (congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m)) HI HM)

noncomputable def row (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : Fin (oldRank P D q) :=
  ⟨IntegralMixedHeightTableQueryBits.oldRow P q,
    (IntegralMixedHeightTableQueryBits.oldRow_lt P q).trans_eq (IntegralMixedOldHeightBits.oldRank_eq P D q).symm⟩
noncomputable def col (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : Fin (oldRank P D q) :=
  ⟨IntegralMixedHeightTableQueryBits.oldCol P q,
    (IntegralMixedHeightTableQueryBits.oldCol_lt P q).trans_eq (IntegralMixedOldHeightBits.oldRank_eq P D q).symm⟩

theorem matrix_entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))) :
    matrix P D q i.val = Algebra.leftMulMatrix (state P D q).sampler.scalarPrefix.basis.finBasis
      (IntegralMixedHistory.cleared (state P D q) i) (row P D q) (col P D q) := by
  have HV : i.val < (bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) ∧
      IntegralMixedHeightTableQueryBits.oldRow P q < oldRank P D q ∧
      IntegralMixedHeightTableQueryBits.oldCol P q < oldRank P D q := ⟨i.isLt, (row P D q).isLt, (col P D q).isLt⟩
  unfold matrix IntegralMixedOldHeightBankBits.sourceEntry
  split_ifs with HC
  · rfl
  · exact False.elim (HC HV)

theorem entryWord_height (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedHeightTablePassBits.entryWord P D q (birth P q + i) = residueBits (matrix P D q i : ZMod (modulus P q)) := by
  rw [IntegralMixedHeightTablePassBits.entryWord, dite_eq_right (by omega), show birth P q + i - birth P q = i by omega]
  exact query_value P D q i hi

theorem number_height (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    IntegralMixedHeightTableReadBits.number P (pair q (IntegralMixedHeightTablePassBits.value P D q)) (birth P q + i) =
      (matrix P D q i : ZMod (modulus P q)).val := by
  rw [IntegralMixedHeightTableReadBits.number_value P D q _ (by unfold IntegralMixedHeightTablePassBits.count; omega)]
  change Nat.fromBitsLE (IntegralMixedHeightTablePassBits.entryWord P D q (birth P q + i)) = _
  rw [entryWord_height P D q i hi]
  exact Nat.fromBitsLE_bits _

end LeanCanny.Algebra.IntegralMixedHeightTableMatrixBits
