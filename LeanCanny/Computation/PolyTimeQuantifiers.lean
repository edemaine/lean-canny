/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimePairing

/-! # Native bounded polynomial-time quantification -/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

theorem unaryPair_computable : ComputableTidilyInPolyTime
    (fun p : List Bool × ℕ => pair p.1 (List.replicate p.2 true))
    (encPair encBits encUnary) encBits :=
  pair_computable (ComputableTidilyInPolyTime.fst encBits encUnary)
    (ComputableTidilyInPolyTime.snd encBits encUnary).encoded

theorem FPPred.forall_lt {n : List Bool → ℕ} {p : List Bool → Prop}
    (hn : UnaryFn n) (hp : FPPred p) :
    FPPred (fun z => ∀ i < n z, p (pair z (List.replicate i true))) := by
  classical
  refine .of_computable (ComputableTidilyInPolyTime.allWithInput
    (test := fun z i => decide (p (pair z (List.replicate i true))))
    (ComputableTidilyInPolyTime.range.comp hn)
    (hp.computable.comp unaryPair_computable)) fun z => ?_
  simp only [List.all_eq_true, Function.comp_apply, List.mem_range, decide_eq_true_eq]

theorem FPPred.exists_lt {n : List Bool → ℕ} {p : List Bool → Prop}
    (hn : UnaryFn n) (hp : FPPred p) :
    FPPred (fun z => ∃ i < n z, p (pair z (List.replicate i true))) := by
  classical
  refine .of_computable (ComputableTidilyInPolyTime.anyWithInput
    (test := fun z i => decide (p (pair z (List.replicate i true))))
    (ComputableTidilyInPolyTime.range.comp hn)
    (hp.computable.comp unaryPair_computable)) fun z => ?_
  simp only [List.any_eq_true, Function.comp_apply, List.mem_range, decide_eq_true_eq]

end LeanCanny
