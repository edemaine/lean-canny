/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramCharacteristicSource

/-! # Gram matrix data retain the literal saved parent under output retargeting -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramCharacteristicSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits IntegralMixedGramCharacteristicSource
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis IntegralMixedValueDoubleNilpotent.matrix

noncomputable def physical (F : Family) (j : ℕ) : Source :=
  IntegralMixedValueDeterminantSource.source F (IntegralMixedValueHomogeneousSnapshot.pointIndices F j) (zeroChoice F)
noncomputable def physicalTable (F : Family) (key : List Bool) (j a b r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (fun i k => IntegralCriticalTotalSnapshotBits.integerEntry ((physical F j).entryMatrix key i k) r t) a b

theorem table_snapshot (P : Parameters) (F : Family) (q : List Bool) (a b r t : ℕ) :
    table P F q a b r t = physicalTable F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) a b r t := by
  rfl

theorem table_transport (P : Parameters) (F : Family) (q c : List Bool) (a b r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 c = get P .slot13 q) : table P F c a b r t = table P F q a b r t := by
  rw [table_snapshot, table_snapshot, hs, hj]

theorem table_current (P : Parameters) (F : Family) (q : List Bool) :
    table P F q (get P .slot8 q) (get P .slot9 q) (get P .row q) (get P .col q) =
      IntegralMixedValueGramSumSource.totalEntry P F q := by
  by_cases H1 : get P .slot8 q < (source P F).dimension q
  · by_cases H2 : get P .slot9 q < (source P F).dimension q
    · by_cases H3 : get P .row q < (source P F).rank q
      · by_cases H4 : get P .col q < (source P F).rank q
        · have HL : IntegralMixedValueGramSumSource.Labels P F q := ⟨H1, H2, H3, H4⟩
          rw [IntegralMixedValueGramSumSource.totalEntry, dite_eq_left HL]
          exact (table_finite P F q ⟨_, H1⟩ ⟨_, H2⟩ ⟨_, H3⟩ ⟨_, H4⟩).trans
            (source_entry P F q _ _ _ _)
        · have HL : ¬IntegralMixedValueGramSumSource.Labels P F q := fun H => H4 H.2.2.2
          rw [IntegralMixedValueGramSumSource.totalEntry, dite_eq_right HL]
          simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, H1, H2, H3, H4, dite_eq_left, dite_false]
      · have HL : ¬IntegralMixedValueGramSumSource.Labels P F q := fun H => H3 H.2.2.1
        rw [IntegralMixedValueGramSumSource.totalEntry, dite_eq_right HL]
        simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, H1, H2, H3, dite_eq_left, dite_false]
    · have HL : ¬IntegralMixedValueGramSumSource.Labels P F q := fun H => H2 H.2.1
      rw [IntegralMixedValueGramSumSource.totalEntry, dite_eq_right HL]
      simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, H1, H2, dite_eq_left, dite_false]
  · have HL : ¬IntegralMixedValueGramSumSource.Labels P F q := fun H => H1 H.1
    rw [IntegralMixedValueGramSumSource.totalEntry, dite_eq_right HL]
    simp only [table, IntegralCriticalTotalSnapshotBits.integerEntry, H1, dite_false]

end LeanCanny.Algebra.IntegralMixedGramCharacteristicSnapshot
