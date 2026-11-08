/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionQuantifiers
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native scans with binary counts and indices

Both the loop count and the index stay binary. No bound on the running time
of a space-bounded child is needed, and no list of child results is stored.
-/

@[expose] public section
namespace LeanCanny.Computation.SpaceFunction
open Turing.MultiTapeTM LeanCanny.Encoding.Brackets
open scoped Classical

theorem forall_binary {test : List Bool → List Bool} {count : List Bool → ℕ}
    (ht : SpaceFunction test) (hn : BinaryFn count) :
    SpaceFunction (fun c => [decide (∀ k < count c,
      test (pair c (BinaryNatCode.encode k)) = [true])]) := by
  have hp := ComputableTidilyInPolyTime.fst encBits encNat
  have hk := ComputableTidilyInPolyTime.snd encBits encNat
  have hq := pair_computable hp (natBits_computable.comp hk)
  have he := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have hc := (ComputableInPolySpace.of_tidyPolyTime he).comp
    (ht.computable.comp (.of_tidyPolyTime hq))
  have hall := ImplicitGraph.forall_below_computable hc hn
  let L : Language := {c | ∀ k < count c, test (pair c (BinaryNatCode.encode k)) = [true]}
  have hd : SpaceDecider L := SpaceDecider.of_computable hall (fun c => by
    simp only [L, Set.mem_ofPred_eq, Function.comp_apply, decide_eq_true_eq]
    rfl)
  exact hd.flagEvaluator.congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [L, Set.mem_ofPred_eq, decide_eq_true_eq])

end LeanCanny.Computation.SpaceFunction
