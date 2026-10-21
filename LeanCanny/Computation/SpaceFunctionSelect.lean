/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionChain

/-! # Branching on a space-bounded computed bit

Native composition computes the predicate bit, then the conditional combinator
runs the selected space-bounded branch. No saved-state protocol is exposed. -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity
open LeanCanny.Encoding

theorem select {pred f g : List Bool → List Bool}
    (P : SpaceFunction pred) (L : SpaceFunction f) (R : SpaceFunction g) :
    SpaceFunction (fun c => if (pred c)[0]?.getD false then f c else g c) := by
  have hp : (fun p : List Bool => [p[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  exact ⟨((Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime
    (TidyFP.of_flag hp)).comp P.computable).ite L.computable R.computable⟩

end LeanCanny.Computation.SpaceFunction
