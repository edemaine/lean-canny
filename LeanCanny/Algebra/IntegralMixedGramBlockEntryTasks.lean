/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramCharacteristicSnapshot

/-! # Native integer-block entries delegate actual Gram scalar entries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramBlockEntryTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def spatialRow (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  get P .row q / IntegralMixedValueGramProductTasks.rank P F q
noncomputable def spatialCol (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  get P .col q / IntegralMixedValueGramProductTasks.rank P F q
noncomputable def basisRow (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  get P .row q % IntegralMixedValueGramProductTasks.rank P F q
noncomputable def basisCol (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  get P .col q % IntegralMixedValueGramProductTasks.rank P F q

theorem spatialRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (spatialRow P F) :=
  (get_binary P a .row).div (IntegralMixedValueGramProductTasks.rank_binary P a F h)
theorem spatialCol_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (spatialCol P F) :=
  (get_binary P a .col).div (IntegralMixedValueGramProductTasks.rank_binary P a F h)
theorem basisRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (basisRow P F) :=
  (get_binary P a .row).mod (IntegralMixedValueGramProductTasks.rank_binary P a F h)
theorem basisCol_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (basisCol P F) :=
  (get_binary P a .col).mod (IntegralMixedValueGramProductTasks.rank_binary P a F h)
theorem spatialRow_cap (P : Parameters) (F : Family) (q : List Bool) : spatialRow P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.div_le_self _ _).trans (get_le P .row q)
theorem spatialCol_cap (P : Parameters) (F : Family) (q : List Bool) : spatialCol P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.div_le_self _ _).trans (get_le P .col q)
theorem basisRow_cap (P : Parameters) (F : Family) (q : List Bool) : basisRow P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.mod_le _ _).trans (get_le P .row q)
theorem basisCol_cap (P : Parameters) (F : Family) (q : List Bool) : basisCol P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.mod_le _ _).trans (get_le P .col q)

noncomputable def first (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscEntry .companion .slot8 (spatialRow P F)
noncomputable def second (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (first P F) .pscEntry .companion .slot9 (spatialCol P F)
noncomputable def third (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (second P F) .pscEntry .companion .row (basisRow P F)
noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (third P F) .pscEntry .companion .col (basisCol P F)
theorem first_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : first P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (spatialRow_binary P a F h)
theorem second_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : second P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a F h) _ _ _ _ (spatialCol_binary P a F h)
theorem third_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : third P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (second_FP P a F h) _ _ _ _ (basisRow_binary P a F h)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (third_FP P a F h) _ _ _ _ (basisCol_binary P a F h)

theorem query_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P (third P F) .pscEntry .companion .col _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_saved P (second P F) .pscEntry .companion .row _ q (by decide)).trans
      ((IntegralMixedValueFieldQuery.query_saved P (first P F) .pscEntry .companion .slot9 _ q (by decide)).trans
        (IntegralMixedValueFieldQuery.query_saved P id .pscEntry .companion .slot8 _ q (by decide))))
theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P (third P F) .pscEntry .companion .col _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_modulus P (second P F) .pscEntry .companion .row _ q (by decide)).trans
      ((IntegralMixedValueFieldQuery.query_modulus P (first P F) .pscEntry .companion .slot9 _ q (by decide)).trans
        (IntegralMixedValueFieldQuery.query_modulus P id .pscEntry .companion .slot8 _ q (by decide))))
theorem query_get (P : Parameters) (F : Family) (q : List Bool) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 2 else if f = .col then basisCol P F q else
      if f = .row then basisRow P F q else if f = .slot9 then spatialCol P F q else
        if f = .slot8 then spatialRow P F q else get P f q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_get,
    IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (basisCol_cap P F q), min_eq_left (basisRow_cap P F q),
    min_eq_left (spatialCol_cap P F q), min_eq_left (spatialRow_cap P F q)]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 3) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have HL := IntegralMixedValueFieldQuery.query_length P (third P F) .pscEntry .companion .col (basisCol P F) q
    have HW : wordBudget P (third P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      simp only [third, second, first, IntegralMixedValueFieldQuery.query_root, id_eq]
    exact HL.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (query_birth P F q)
    rw [query, IntegralMixedValueFieldQuery.query_routine, hr]
    decide

end LeanCanny.Algebra.IntegralMixedGramBlockEntryTasks
