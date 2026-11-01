/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryMatrix
/-! # The guarded native PSC entry is the actual natural matrix entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical

theorem table_outside (P : Parameters) (F : Family) (q : List Bool) (i j r t : ℕ)
    (h : ¬(i < (source P F).dimension q ∧ j < (source P F).dimension q ∧
      r < (source P F).rank q ∧ t < (source P F).rank q)) : table P F q i j r t = 0 := by
  by_cases hi : i < (source P F).dimension q
  · by_cases hj : j < (source P F).dimension q
    · by_cases hr : r < (source P F).rank q
      · have ht : ¬t < (source P F).rank q := fun ht => h ⟨hi, hj, hr, ht⟩
        simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, hi, hj, hr, ht, dite_eq_left, dite_false]
      · simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, hi, hj, hr, dite_eq_left, dite_false]
    · simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, hi, hj, dite_eq_left, dite_false]
  · simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, hi, dite_false]

theorem integer_eq (P : Parameters) (F : Family) (q : List Bool) : selectedInteger P F q = integerValue P F q := by
  by_cases hl : Labels P F q
  · let i : Fin ((source P F).dimension q) := ⟨get P .slot9 q, hl.1⟩
    let j : Fin ((source P F).dimension q) := ⟨get P .slot10 q, hl.2.1⟩
    let r : Fin ((source P F).rank q) := ⟨get P .row q, hl.2.2.1⟩
    let t : Fin ((source P F).rank q) := ⟨get P .col q, hl.2.2.2⟩
    change selectedInteger P F q = table P F q i.val j.val r.val t.val
    rw [table_finite, matrix_entry P F q i j r t rfl rfl rfl rfl]
    simp only [selectedInteger, Request, hl.2.2.1, hl.2.2.2, and_true]
  · have hn : ¬Request P F q := fun hr => hl (request_labels P F q hr)
    rw [selectedInteger, ite_eq_right hn]
    exact (table_outside P F q _ _ _ _ hl).symm

theorem value_eq (P : Parameters) (F : Family) (q : List Bool) : selectedValue P F q = value P F q :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (integer_eq P F q)

theorem actual_value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (q : List Bool) (he : RepliesAt P F answer q) :
    (program P F).value answer q = value P F q := (value_at P F g answer q he).trans (value_eq P F q)

end LeanCanny.Algebra.IntegralMixedPscEntryBits
