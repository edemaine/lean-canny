/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMomentSpaceEntries

/-! # Task requests for entries of an augmented moment matrix -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMoment.EntryBits
open LeanCanny.Encoding LeanCanny.Encoding.Brackets

attribute [local irreducible] rowIndex colIndex sinkIndex rowInput columnInput matrixInput

def task (a : Access) (rowTask columnTask matrixTask : List Bool → List Bool)
    (zeroTask : List Bool) (p : List Bool) : List Bool :=
  if rowIndex p = [] then
    if colIndex p = [] then zeroTask
    else if colIndex p = sinkIndex a (pairFst p) then zeroTask else rowTask (rowInput p)
  else if rowIndex p = sinkIndex a (pairFst p) then zeroTask
  else if colIndex p = [] then zeroTask
  else if colIndex p = sinkIndex a (pairFst p) then columnTask (columnInput p)
  else matrixTask (matrixInput p)

theorem task_FP (a : Access) (hd : a.dimension ∈ FP)
    (rowTask columnTask matrixTask : List Bool → List Bool)
    (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) (zeroTask : List Bool) :
    task a rowTask columnTask matrixTask zeroTask ∈ FP := by
  have ER := mem_FP_comp rowInput_mem_FP hr
  have EC := mem_FP_comp columnInput_mem_FP hc
  have EM := mem_FP_comp matrixInput_mem_FP hm
  have hz := constFn_mem_FP zeroTask
  have he := constFn_mem_FP ([] : List Bool)
  have hl := mem_FP_comp pairFst_mem_FP (sinkIndex_mem_FP_of_dimension a hd)
  have hrow := (stringEq_fppred colIndex_mem_FP he).ite_mem_FP hz
    ((stringEq_fppred colIndex_mem_FP hl).ite_mem_FP hz ER)
  have hbody := (stringEq_fppred rowIndex_mem_FP hl).ite_mem_FP hz
    ((stringEq_fppred colIndex_mem_FP he).ite_mem_FP hz
      ((stringEq_fppred colIndex_mem_FP hl).ite_mem_FP EC EM))
  have h := (stringEq_fppred rowIndex_mem_FP he).ite_mem_FP hrow hbody
  exact mem_FP_of_eq h (fun _ => rfl)

theorem task_eq (a : Access) (rowTask columnTask matrixTask answer : List Bool → List Bool)
    (zeroTask : List Bool) (hr : ∀ p, answer (rowTask p) = a.row p)
    (hc : ∀ p, answer (columnTask p) = a.column p) (hm : ∀ p, answer (matrixTask p) = a.entry p)
    (hz : answer zeroTask = []) (p : List Bool) :
    answer (task a rowTask columnTask matrixTask zeroTask p) = entry a p := by
  simp only [task, entry, rowInput, columnInput, matrixInput]
  split_ifs <;> first | exact hz | exact hr _ | exact hc _ | exact hm _

end LeanCanny.Algebra.MatrixMoment.EntryBits
