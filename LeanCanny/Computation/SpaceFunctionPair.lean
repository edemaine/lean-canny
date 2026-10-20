/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionChain

/-! # Pairing outputs of sequential polynomial-space subroutines

The first response and input are retained while the second child runs.
Existing composition certificates bound every saved and child state and clock.
-/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity

def pairOutputsFinish (z : List Bool) : List Bool := pair (pairSnd (pairFst z)) (pairSnd z)

theorem pairOutputsFinish_mem_FP : pairOutputsFinish ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

noncomputable def pairOutputs {f g : List Bool → List Bool} (F : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (fun c => pair (f c) (g c)) := by
  let H := F.withInput.chain ((G.precompose pairFst pairFst_mem_FP).withInput)
  let E := H.postcompose pairOutputsFinish pairOutputsFinish_mem_FP
  exact E.congr (funext fun c => by simp only [Function.comp_apply, pairOutputsFinish, pairFst_pair, pairSnd_pair])

end LeanCanny.Computation.SpaceFunction
