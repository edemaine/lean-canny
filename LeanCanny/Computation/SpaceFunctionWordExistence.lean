/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionWordQuantifiers

/-! # Native bounded existential search over word labels -/

@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open LeanCanny.Encoding.Brackets
open scoped Classical

theorem exists_words {test : List Bool → List Bool} {width : List Bool → ℕ}
    (ht : SpaceFunction test) (hw : UnaryFn width) :
    SpaceFunction (fun c => [decide (∃ w : List Bool, w.length = width c ∧ test (pair c w) = [true])]) := by
  have hn := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have N := (ht.postcompose _ hn).forall_words hw
  exact (N.postcompose _ hn).congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, id_eq, List.cons.injEq, and_true, decide_eq_true_eq,
      not_forall, not_not, exists_prop])

end LeanCanny.Computation.SpaceFunction
