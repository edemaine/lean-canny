/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayBranch

/-! # Two actual rectangular-entry requests for a negative Gram product

Slot 10 is the flattened row/basis summation index. Every written selector
is bounded by an existing task field, even for an out-of-range term. The
two children preserve the same selected parent and original spatial source.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramProductTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def rank (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  count ((IntegralMixedVirtualTaskBits.family P F).birth q + 2) ((IntegralMixedVirtualTaskBits.family P F).width q)
noncomputable def sourceRow (P : Parameters) (F : Family) (q : List Bool) : ℕ := get P .slot10 q / rank P F q
noncomputable def middle (P : Parameters) (F : Family) (q : List Bool) : ℕ := get P .slot10 q % rank P F q
def column (P : Parameters) (left : Bool) (q : List Bool) : ℕ := if left then get P .slot8 q else get P .slot9 q
noncomputable def row (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : ℕ := if left then get P .row q else middle P F q
noncomputable def col (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : ℕ := if left then middle P F q else get P .col q

theorem rank_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (rank P F) := by
  have H := IntegralMixedVirtualTaskBits.metadata P a F h
  exact ((BinaryFn.const 2).powUnary H.width).powUnary (H.birth.add (UnaryFn.const 2))
theorem sourceRow_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (sourceRow P F) :=
  (get_binary P a .slot10).div (rank_binary P a F h)
theorem middle_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (middle P F) :=
  (get_binary P a .slot10).mod (rank_binary P a F h)
theorem column_binary (P : Parameters) (a : Access P) (left : Bool) : BinaryFn (column P left) := by
  cases left <;> exact get_binary P a _
theorem row_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (left : Bool) : BinaryFn (row P F left) := by
  cases left
  · exact middle_binary P a F h
  · exact get_binary P a .row
theorem col_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (left : Bool) : BinaryFn (col P F left) := by
  cases left
  · exact get_binary P a .col
  · exact middle_binary P a F h

theorem sourceRow_cap (P : Parameters) (F : Family) (q : List Bool) : sourceRow P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.div_le_self _ _).trans (get_le P .slot10 q)
theorem middle_cap (P : Parameters) (F : Family) (q : List Bool) : middle P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.mod_le _ _).trans (get_le P .slot10 q)
theorem column_cap (P : Parameters) (left : Bool) (q : List Bool) : column P left q ≤ numericCap P (RankedHistoryTask.root q) := by
  cases left <;> exact get_le P _ q
theorem row_cap (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : row P F left q ≤ numericCap P (RankedHistoryTask.root q) := by
  cases left
  · exact middle_cap P F q
  · exact get_le P .row q
theorem col_cap (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : col P F left q ≤ numericCap P (RankedHistoryTask.root q) := by
  cases left
  · exact get_le P .col q
  · exact middle_cap P F q

noncomputable def first (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscEntry .relativePower .slot8 (sourceRow P F)
noncomputable def second (P : Parameters) (F : Family) (left : Bool) :=
  IntegralMixedValueFieldQuery.query P (first P F) .pscEntry .relativePower .slot9 (column P left)
noncomputable def third (P : Parameters) (F : Family) (left : Bool) :=
  IntegralMixedValueFieldQuery.query P (second P F left) .pscEntry .relativePower .row (row P F left)
noncomputable def query (P : Parameters) (F : Family) (left : Bool) :=
  IntegralMixedValueFieldQuery.query P (third P F left) .pscEntry .relativePower .col (col P F left)

theorem first_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : first P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (sourceRow_binary P a F h)
theorem second_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (left : Bool) : second P F left ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a F h) _ _ _ _ (column_binary P a left)
theorem third_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (left : Bool) : third P F left ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (second_FP P a F h left) _ _ _ _ (row_binary P a F h left)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (left : Bool) : query P F left ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (third_FP P a F h left) _ _ _ _ (col_binary P a F h left)

theorem query_root (P : Parameters) (F : Family) (left : Bool) (q : List Bool) :
    RankedHistoryTask.root (query P F left q) = RankedHistoryTask.root q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem query_birth (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : birth P (query P F left q) = birth P q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem query_saved (P : Parameters) (F : Family) (left : Bool) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F left q) = IntegralMixedVirtualTaskBits.saved P q := by
  exact (IntegralMixedValueFieldQuery.query_saved P (third P F left) .pscEntry .relativePower .col _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_saved P (second P F left) .pscEntry .relativePower .row _ q (by decide)).trans
      ((IntegralMixedValueFieldQuery.query_saved P (first P F) .pscEntry .relativePower .slot9 _ q (by decide)).trans
        (IntegralMixedValueFieldQuery.query_saved P id .pscEntry .relativePower .slot8 _ q (by decide))))
theorem query_modulus (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : modulus P (query P F left q) = modulus P q := by
  exact (IntegralMixedValueFieldQuery.query_modulus P (third P F left) .pscEntry .relativePower .col _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_modulus P (second P F left) .pscEntry .relativePower .row _ q (by decide)).trans
      ((IntegralMixedValueFieldQuery.query_modulus P (first P F) .pscEntry .relativePower .slot9 _ q (by decide)).trans
        (IntegralMixedValueFieldQuery.query_modulus P id .pscEntry .relativePower .slot8 _ q (by decide))))

theorem query_get (P : Parameters) (F : Family) (left : Bool) (q : List Bool) (f : Field) :
    get P f (query P F left q) = if f = .slot14 then 2 else if f = .col then col P F left q else
      if f = .row then row P F left q else if f = .slot9 then column P left q else
        if f = .slot8 then sourceRow P F q else get P f q := by
  simp only [query, third, second, first, IntegralMixedValueFieldQuery.query_get,
    IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (col_cap P F left q), min_eq_left (row_cap P F left q),
    min_eq_left (column_cap P left q), min_eq_left (sourceRow_cap P F q)]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (left : Bool) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 25) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F left q) := by
  refine ⟨query_root P F left q, ?_, ?_⟩
  · have HL := IntegralMixedValueFieldQuery.query_length P (third P F left) .pscEntry .relativePower .col (col P F left) q
    have HW : wordBudget P (third P F left q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      simp only [third, second, first, IntegralMixedValueFieldQuery.query_root, id_eq]
    exact HL.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (query_birth P F left q)
    · rw [query, IntegralMixedValueFieldQuery.query_routine, hr]
      rfl
    · rw [query, IntegralMixedValueFieldQuery.query_phase, hp]
      decide

end LeanCanny.Algebra.IntegralMixedValueGramProductTasks
