/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
/-! # Native existential scans with binary counts and indices -/
@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open LeanCanny.Encoding.Brackets
open scoped Classical

theorem exists_binary {test : List Bool → List Bool} {count : List Bool → ℕ}
    (ht : SpaceFunction test) (hn : BinaryFn count) :
    SpaceFunction (fun c => [decide (∃ k < count c,
      test (pair c (BinaryNatCode.encode k)) = [true])]) := by
  have EN := ht.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have EA := EN.forall_binary hn
  have EF := EA.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact EF.congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,id_eq,List.cons.injEq,and_true,decide_eq_true_eq,
      not_forall,not_not,exists_prop])

end LeanCanny.Computation.SpaceFunction
