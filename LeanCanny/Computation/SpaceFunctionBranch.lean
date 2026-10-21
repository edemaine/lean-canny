/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Polynomial-time functions and branches in the tidy space calculus -/

@[expose] public section

namespace LeanCanny.Computation.SpaceFunction
open Complexity Turing.MultiTapeTM

theorem ofFP (f : List Bool → List Bool) (hf : f ∈ FP) : SpaceFunction f :=
  ⟨ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_mem_FP hf)⟩

theorem branch {f g : List Bool → List Bool} (pred : List Bool → Bool)
    (hp : (fun x => [pred x]) ∈ FP) (L : SpaceFunction f) (R : SpaceFunction g) :
    SpaceFunction (fun x => if pred x then f x else g x) :=
  ⟨(ComputableTidilyInPolySpace.of_polyTime (TidyFP.of_flag hp)).ite
    L.computable R.computable⟩

end LeanCanny.Computation.SpaceFunction
