/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDecider

/-! # Native PSPACE closure under union

The tidy machine conditional first decides the left language and otherwise
runs the right decision procedure.
-/

@[expose] public section

namespace LeanCanny.Computation
open Turing.MultiTapeTM
open scoped Classical

theorem SpaceDecider.union {L M : Language} (D : SpaceDecider L) (E : SpaceDecider M) :
    SpaceDecider (L ∪ M) := by
  have ht := ComputableTidilyInPolySpace.of_polyTime
    (ComputableTidilyInPolyTime.const (encIn := encBits) (encMid := encBool) true)
  apply SpaceDecider.of_computable (D.computable.ite ht E.computable)
  intro x
  by_cases hx : x ∈ L <;> simp only [Set.mem_union, hx, decide_true, decide_false,
    Bool.false_eq_true, ite_true, ite_false, decide_eq_true_eq, true_or, false_or]

theorem mem_PSPACE_union {L M : Language} (hL : L ∈ PSPACE) (hM : M ∈ PSPACE) :
    L ∪ M ∈ PSPACE :=
  ((SpaceDecider.ofPSPACE hL).union (SpaceDecider.ofPSPACE hM)).mem_PSPACE

end LeanCanny.Computation
