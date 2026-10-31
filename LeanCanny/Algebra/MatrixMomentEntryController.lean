/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMomentSpaceEntries
public import LeanCanny.Computation.ControllerRequests

/-! # Resumable augmented-moment entry routing

The existing augmented matrix selector chooses a row, column, original
entry, or local zero. Replacing its readers by task writers gives the
request itself; replacing them by a marker gives the request flag. No
child evaluator is used in the native controller certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.MatrixMoment.EntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def routed (a : Access) (rowTask columnTask matrixTask : List Bool → List Bool) : Access :=
  { a with row := rowTask, column := columnTask, entry := matrixTask }

def marked (a : Access) : Access := routed a (fun _ => [true]) (fun _ => [true]) (fun _ => [true])

noncomputable def program (a : Access) (input rowTask columnTask matrixTask : List Bool → List Bool) : SingleCall.Program where
  request p := decide (entry (marked a) (input p) = [true])
  query p := entry (routed a rowTask columnTask matrixTask) (input p)
  immediate _ := []
  finish := pairSnd

attribute [local irreducible] BinaryNat.pred BinaryNat.succ

theorem program_controls (a : Access) (hd : a.dimension ∈ FP) (input rowTask columnTask matrixTask : List Bool → List Bool)
    (hi : input ∈ FP) (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) :
    (program a input rowTask columnTask matrixTask).Controls := by
  have HF : (entry (marked a) ∘ input) ∈ FP :=
    mem_FP_comp hi (entry_mem_FP (marked a) ⟨hd, constFn_mem_FP _, constFn_mem_FP _, constFn_mem_FP _⟩)
  have HQ : (entry (routed a rowTask columnTask matrixTask) ∘ input) ∈ FP :=
    mem_FP_comp hi (entry_mem_FP (routed a rowTask columnTask matrixTask) ⟨hd, hr, hc, hm⟩)
  exact ⟨(stringEq_fppred HF (constFn_mem_FP [true])).flag_mem_FP, HQ, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem program_value (a : Access) (input rowTask columnTask matrixTask answer : List Bool → List Bool)
    (hr : ∀ p, answer (rowTask p) = a.row p)
    (hc : ∀ p, answer (columnTask p) = a.column p)
    (hm : ∀ p, answer (matrixTask p) = a.entry p) (p : List Bool) :
    (program a input rowTask columnTask matrixTask).value answer p = entry a (input p) := by
  simp only [SingleCall.Program.value, program, marked, routed, entry, sinkIndex]
  split_ifs <;> simp_all

theorem program_requests_iff (a : Access) (input rowTask columnTask matrixTask answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p q : List Bool) :
    (program a input rowTask columnTask matrixTask).controller.Requests answer budget p q ↔
      entry (marked a) (input p) = [true] ∧ q = entry (routed a rowTask columnTask matrixTask) (input p) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

end LeanCanny.Algebra.MatrixMoment.EntryBits
