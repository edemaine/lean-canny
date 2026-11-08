/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Streamed native scans of every word of a unary width -/

@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM LeanCanny.Encoding.Brackets
open scoped Classical

theorem forall_words {test : List Bool → List Bool} {width : List Bool → ℕ}
    (ht : SpaceFunction test) (hw : UnaryFn width) :
    SpaceFunction (fun c => [decide (∀ w : List Bool, w.length = width c → test (pair c w) = [true])]) := by
  have hp := ComputableTidilyInPolyTime.fst encBits encBits
  have hu := ComputableTidilyInPolyTime.snd encBits encBits
  have hq := pair_computable hp hu
  have he := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have hc := (ComputableInPolySpace.of_tidyPolyTime he).comp
    (ht.computable.comp (.of_tidyPolyTime hq))
  have hall := ImplicitGraph.forall_words_computable hc hw
  let L : Language := {c | ∀ w : List Bool, w.length = width c → test (pair c w) = [true]}
  have hd : SpaceDecider L := SpaceDecider.of_computable hall (fun c => by
    simp only [L, Set.mem_ofPred_eq, decide_eq_true_eq]
    rfl)
  exact hd.flagEvaluator.congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [L, Set.mem_ofPred_eq, decide_eq_true_eq])

end LeanCanny.Computation.SpaceFunction
