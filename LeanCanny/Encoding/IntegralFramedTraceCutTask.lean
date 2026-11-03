/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineContextQuery
public import LeanCanny.Encoding.IntegralFramedCreatingCut
/-! # Native chronological cut probes retain one original root

The datum is `(unary birth, coefficient/choice selectors)`. Every probe
starts from a fresh task at the literal original root with fixed virtual
context2. Actual cut kind and rule come from the creating instruction.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutTask
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def stage (z : List Bool) : ℕ := (pairFst (pairSnd z)).length
def selectors (z : List Bool) : List Bool := pairSnd (pairSnd z)
def base (z : List Bool) : List Bool := RankedHistoryTask.pack (pairFst z) 0 0 []
theorem stage_unary : UnaryFn stage:=UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem selectors_FP : selectors∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem base_FP : base∈FP:=mem_FP_pair pairFst_mem_FP (constFn_mem_FP _)

def prepare (z : List Bool) := pair (pairFst z) (pair (pairFst (pairSnd z)) [])
theorem prepare_FP : prepare∈FP:=mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP []))

def task (P : Parameters) : List Bool→List Bool :=
  IntegralMixedRoutineContextQuery.query P base stage .rawFactor .companion (fun _=>0) (fun _=>2)∘prepare
theorem task_FP (P : Parameters) (a : Access P) : task P∈FP:=
  mem_FP_comp prepare_FP (IntegralMixedRoutineContextQuery.query_FP P a base base_FP stage (BinaryFn.ofUnary stage_unary)
    .rawFactor .companion _ _ (BinaryFn.const 0) (BinaryFn.const 2))

theorem task_root (P : Parameters) (z : List Bool) : RankedHistoryTask.root (task P z)=pairFst z := by
  have H:=IntegralMixedRoutineContextQuery.query_root P base stage .rawFactor .companion (fun _=>0) (fun _=>2) (prepare z)
  simpa only [task,Function.comp_apply,base,prepare,RankedHistoryTask.root_pack,pairFst_pair] using H

theorem task_birth (P : Parameters) (z : List Bool) (hb : stage z≤birthCap P (pairFst z)) : birth P (task P z)=stage z := by
  have HB : stage (prepare z)≤birthCap P (RankedHistoryTask.root (base (prepare z))) := by
    simpa only [base,prepare,stage,RankedHistoryTask.root_pack,pairFst_pair,pairSnd_pair] using hb
  have H:=IntegralMixedRoutineContextQuery.query_birth P base stage .rawFactor .companion (fun _=>0) (fun _=>2) (prepare z) HB
  simpa only [task,Function.comp_apply,prepare,stage,pairFst_pair,pairSnd_pair] using H

theorem task_context (P : Parameters) (z : List Bool) : get P .slot15 (task P z)=2 := by
  apply IntegralMixedRoutineContextQuery.query_context P base stage .rawFactor .companion _ _ (prepare z)
  exact (by decide : 2≤6).trans (IntegralMixedRoutineTaskBits.routine_cap P _)

theorem task_saved (P : Parameters) (z : List Bool) (hb : stage z≤birthCap P (pairFst z)) :
    IntegralMixedVirtualTaskBits.saved P (task P z)=IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst z) (stage z) (BinaryNatCode.encode 2) := by
  unfold IntegralMixedVirtualTaskBits.saved
  rw [task_root,task_birth P z hb,task_context]

def reindex (P : Parameters) (z : List Bool) : List Bool := pair (task P z) (selectors z)
theorem reindex_FP (P : Parameters) (a : Access P) : reindex P∈FP:=mem_FP_pair (task_FP P a) selectors_FP

@[simp] theorem stage_packet (r u d : List Bool) : stage (pair r (pair u d))=u.length := by
  simp only [stage,pairFst_pair,pairSnd_pair]
@[simp] theorem selectors_packet (r u d : List Bool) : selectors (pair r (pair u d))=d := by
  simp only [selectors,pairSnd_pair]

theorem task_selectors (P : Parameters) (r u d e : List Bool) :
    task P (pair r (pair u d))=task P (pair r (pair u e)) := by
  simp only [task,Function.comp_apply,prepare,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralFramedTraceCutTask
