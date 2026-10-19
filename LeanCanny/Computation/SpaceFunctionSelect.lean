/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionChain

/-!
# Branching on a space-bounded computed bit

First compute the predicate while retaining the input, then run the selected
child. Sequential and branch certificates include the predicate computation,
the saved input/response, and the selected child in the physical space/clock.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity
open LeanCanny.Encoding

noncomputable def select {pred f g : List Bool → List Bool}
    (P : SpaceFunction pred) (L : SpaceFunction f) (R : SpaceFunction g) :
    SpaceFunction (fun c => if (pred c)[0]?.getD false then f c else g c) := by
  have hp : (fun p : List Bool => [(pairSnd p)[0]?.getD false]) ∈ FP :=
    (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).flag_mem_FP
  let B := branch (fun p => (pairSnd p)[0]?.getD false) hp
    (L.precompose pairFst pairFst_mem_FP) (R.precompose pairFst pairFst_mem_FP)
  let E := P.withInput.chain B
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]

end LeanCanny.Computation.SpaceFunction
