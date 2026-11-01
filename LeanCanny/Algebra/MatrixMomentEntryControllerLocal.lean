/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MatrixMomentEntryController
/-! # Guarded local replies and exact row/column/interior request cases -/
@[expose] public section
namespace LeanCanny.Algebra.MatrixMoment.EntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev RepliesAt (a : Access) (input rowTask columnTask matrixTask answer : List Bool → List Bool) (p : List Bool) : Prop :=
  (rowIndex (input p) = [] → colIndex (input p) ≠ [] → colIndex (input p) ≠ sinkIndex a (pairFst (input p)) →
    answer (rowTask (pair (pairFst (input p)) (BinaryNat.pred (colIndex (input p))))) =
      a.row (pair (pairFst (input p)) (BinaryNat.pred (colIndex (input p))))) ∧
  (rowIndex (input p) ≠ [] → rowIndex (input p) ≠ sinkIndex a (pairFst (input p)) → colIndex (input p) ≠ [] →
    colIndex (input p) = sinkIndex a (pairFst (input p)) →
    answer (columnTask (pair (pairFst (input p)) (BinaryNat.pred (rowIndex (input p))))) =
      a.column (pair (pairFst (input p)) (BinaryNat.pred (rowIndex (input p))))) ∧
  (rowIndex (input p) ≠ [] → rowIndex (input p) ≠ sinkIndex a (pairFst (input p)) → colIndex (input p) ≠ [] →
    colIndex (input p) ≠ sinkIndex a (pairFst (input p)) →
    answer (matrixTask (pair (pairFst (input p)) (pair (BinaryNat.pred (rowIndex (input p))) (BinaryNat.pred (colIndex (input p)))))) =
      a.entry (pair (pairFst (input p)) (pair (BinaryNat.pred (rowIndex (input p))) (BinaryNat.pred (colIndex (input p))))))

theorem program_value_local (a : Access) (input rowTask columnTask matrixTask answer : List Bool → List Bool)
    (p : List Bool) (he : RepliesAt a input rowTask columnTask matrixTask answer p) :
    (program a input rowTask columnTask matrixTask).value answer p = entry a (input p) := by
  obtain ⟨hr, hc, hm⟩ := he
  simp only [SingleCall.Program.value, program, marked, routed, entry, sinkIndex]
  split_ifs <;> simp_all [sinkIndex]

theorem routed_cases (a : Access) (rowTask columnTask matrixTask : List Bool → List Bool) (p : List Bool)
    (h : entry (marked a) p = [true]) :
    entry (routed a rowTask columnTask matrixTask) p = rowTask (pair (pairFst p) (BinaryNat.pred (colIndex p))) ∨
    entry (routed a rowTask columnTask matrixTask) p = columnTask (pair (pairFst p) (BinaryNat.pred (rowIndex p))) ∨
    entry (routed a rowTask columnTask matrixTask) p = matrixTask
      (pair (pairFst p) (pair (BinaryNat.pred (rowIndex p)) (BinaryNat.pred (colIndex p)))) := by
  simp only [entry, marked, routed, sinkIndex] at h ⊢
  split_ifs at h ⊢ <;> simp_all

end LeanCanny.Algebra.MatrixMoment.EntryBits
