/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatClearedHeightRequery

/-! # Natural-index views of actual retained bank matrix entries

These views package the dependent state and basis behind natural metadata.
Clipping an invalid retained selector cannot create a valid numerator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def State.natEntry {S B n W D C m : ℕ} (x : State S B n W D C m) (i r t modulus : ℕ) : List Bool :=
  x.entry (if hi : i < m then some ⟨i, hi⟩ else none)
    ⟨r % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count m B, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ modulus

theorem State.natEntry_fin {S B n W D C m : ℕ} (x : State S B n W D C m) (i modulus : ℕ)
    (r t : Fin (count m B)) :
    x.natEntry i r.val t.val modulus = x.entry (if hi : i < m then some ⟨i, hi⟩ else none) r t modulus := by
  unfold State.natEntry
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

theorem State.natEntry_invalid {S B n W D C m : ℕ} (x : State S B n W D C m) (i r t modulus : ℕ) (hi : ¬ i < m) :
    x.natEntry i r t modulus = [] := by
  unfold State.natEntry
  rw [dite_eq_right hi, State.entry_none]

theorem State.natEntry_min {S B n W D C m : ℕ} (x : State S B n W D C m) (i r t modulus cap : ℕ) (hc : m ≤ cap) :
    x.natEntry (min i cap) r t modulus = x.natEntry i r t modulus := by
  by_cases hi : i < m
  · rw [min_eq_left (hi.le.trans hc)]
  · rw [State.natEntry_invalid _ _ _ _ _ hi, State.natEntry_invalid _ _ _ _ _ (by omega)]

end LeanCanny.Algebra.IntegralCriticalScript

namespace LeanCanny.Algebra.CommonHeightBits
open LeanCanny.Encoding MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem Source.rawValue_zero (S : Source) (c : List Bool)
    (hz : letI := S.ring c; S.numerator c = 0) : S.rawValue c = [] := by
  let := S.ring c
  unfold Source.rawValue
  dsimp only
  rw [hz, map_zero, Matrix.zero_apply, Int.cast_zero]
  simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.CommonHeightBits

namespace LeanCanny.Algebra.IntegralCriticalScriptHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript
set_option backward.isDefEq.respectTransparency false

theorem rawValue_natEntry (F : Queries) (c : List Bool) :
    (source F).rawValue c = if F.coordinate c < F.ambient c + 1 then
      (state F c).natEntry (F.selector c (F.coordinate c)) (F.row c).val (F.col c).val (F.modulus c) else [] := by
  by_cases hc : F.coordinate c < F.ambient c + 1
  · rw [ite_eq_left hc, State.natEntry_fin, rawValue_entry F c hc]
    rfl
  · rw [ite_eq_right hc]
    apply CommonHeightBits.Source.rawValue_zero
    let := (source F).ring c
    change (if F.coordinate c < F.ambient c + 1 then _ else 0) = 0
    exact ite_eq_right hc

end LeanCanny.Algebra.IntegralCriticalScriptHeightBits

namespace LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatHeightBits
set_option backward.isDefEq.respectTransparency false

noncomputable def bankValue (F : Scripts) (r : List Bool) (j i row col modulus : ℕ) : List Bool :=
  (stateAt (F.rules r) (F.length_le r) (F.scalar_bound r) j).natEntry i row col modulus

theorem rawValue_bank (F : Scripts) (q : List Bool) :
    rawValue F q = bankValue F (root q) (length F q)
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q) (row F q) (col F q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) := by
  have H := IntegralCriticalScriptHeightBits.rawValue_natEntry (heightQueries F) q
  rw [ite_eq_left (show (heightQueries F).coordinate q < (heightQueries F).ambient q + 1 from Nat.succ_pos _)] at H
  exact H

theorem sourceRawValue_bank (F : Scripts) (q : List Bool) :
    (IntegralCriticalScriptHeightBits.source (queries F)).rawValue q =
      if coordinate F q < F.ambient (root q) + 1 then
        bankValue F (root q) (length F q) (selected F q) (row F q) (col F q)
          (IntegralCriticalHistoryTask.modulus F.toParameters q) else [] :=
  IntegralCriticalScriptHeightBits.rawValue_natEntry (queries F) q

theorem rawTask_rawValue (F : Scripts) (q : List Bool) :
    rawValue F (rawTask F q) = (IntegralCriticalScriptHeightBits.source (queries F)).rawValue q := by
  rw [rawValue_bank, sourceRawValue_bank, rawTask_root, rawTask_length, rawTask_row, rawTask_col, rawTask_modulus, rawTask_get]
  change bankValue F (root q) (length F q)
    (min (selected F q) (IntegralCriticalHistoryTask.numericCap F.toParameters (root q))) _ _ _ = _
  have HL : (past (F.rules (root q)) (length F q)).length = length F q :=
    (past_length _ _).trans (min_eq_left (length_le_full F q))
  have HC : (past (F.rules (root q)) (length F q)).length ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
    HL.le.trans ((length_le_cap F q).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1)
  unfold bankValue
  rw [State.natEntry_min _ _ _ _ _ _ HC]
  split_ifs with hi
  · rfl
  · apply State.natEntry_invalid
    rw [HL]
    unfold selected
    rw [selector_outside F q (coordinate F q) hi]
    exact not_lt_of_ge (length_le_birth F q)

end LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
