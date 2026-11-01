/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueCharacteristicExtraction
/-! # A native reflected-digit request for the relative value factor

Slot 8 is the finite trailing-coefficient label. Its modulo decoder is
explicit; the raw-source decoder must validate the original choice label
before using this branch. The chosen spatial coordinate stays in slot 13.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueFactorTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def choice (P : Parameters) (F : Family) (q : List Bool) :
    Fin (IntegralMixedValueTrailing.ChoiceBound
      ((IntegralMixedVirtualTaskBits.family P F).spatial q) ((IntegralMixedVirtualTaskBits.family P F).rule q)) :=
  ⟨get P .slot8 q % (IntegralMixedGridValue.dimension
    ((IntegralMixedVirtualTaskBits.family P F).spatial q) ((IntegralMixedVirtualTaskBits.family P F).rule q) + 2),
      Nat.mod_lt _ (by omega)⟩

theorem choice_value (P : Parameters) (F : Family) (q : List Bool)
    (h : get P .slot8 q < IntegralMixedValueTrailing.ChoiceBound
      ((IntegralMixedVirtualTaskBits.family P F).spatial q) ((IntegralMixedVirtualTaskBits.family P F).rule q)) :
    (choice P F q).val = get P .slot8 q := Nat.mod_eq_of_lt h

theorem choice_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (fun q => (choice P F q).val) :=
  (get_binary P a .slot8).mod
    ((IntegralMixedValueDeterminantMetadata.dimension_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)).add (BinaryFn.const 2))

noncomputable def selectedRow (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  (IntegralMixedValueDeterminantSource.row (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) (choice P F) q).val
noncomputable def selectedCol (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  (IntegralMixedValueDeterminantSource.col (IntegralMixedVirtualTaskBits.family P F)
    (IntegralMixedVirtualTaskBits.indices P F) q).val

theorem row_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (selectedRow P F) :=
  IntegralMixedValueDeterminantMetadata.row_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h) _
    (choice_binary P a F h)
theorem col_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (selectedCol P F) :=
  IntegralMixedValueDeterminantMetadata.col_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)

theorem row_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) : selectedRow P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  apply le_trans (Fin.isLt _).le
  exact (IntegralMixedGramCharacteristicBounds.rank_le P F g q hv).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

theorem col_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) : selectedCol P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  apply le_trans (Fin.isLt _).le
  exact (IntegralMixedGramCharacteristicBounds.rank_le P F g q hv).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

noncomputable def first (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscDeterminant .relativePower .row (selectedRow P F)
noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (first P F) .pscDeterminant .relativePower .col (selectedCol P F)
theorem first_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : first P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (row_binary P a F h)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a F h) _ _ _ _ (col_binary P a F h)

theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P (first P F) .pscDeterminant .relativePower .col _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P id .pscDeterminant .relativePower .row _ q (by decide))
theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P (first P F) .pscDeterminant .relativePower .col _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_modulus P id .pscDeterminant .relativePower .row _ q (by decide))
theorem query_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 3 else if f = .col then selectedCol P F q else
      if f = .row then selectedRow P F q else get P f q := by
  simp only [query, first, IntegralMixedValueFieldQuery.query_get, IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (row_cap P F g q hv), min_eq_left (col_cap P F g q hv)]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 4) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have H := IntegralMixedValueFieldQuery.query_length P (first P F) .pscDeterminant .relativePower .col (selectedCol P F) q
    have HW : wordBudget P (first P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [first, IntegralMixedValueFieldQuery.query_root]
      rfl
    exact H.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (query_birth P F q)
    rw [query, IntegralMixedValueFieldQuery.query_routine, hr]
    decide

end LeanCanny.Algebra.IntegralMixedValueFactorTasks
