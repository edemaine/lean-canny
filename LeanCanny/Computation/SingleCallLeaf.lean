/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SingleCallController
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native leaf computations in a one-request recursive controller

Leaves compute their output locally in polynomial space and request no child.
The recursive branch retains its original query, reply processing, and state
type. No leaf execution clock or additional saved state is introduced.
-/

@[expose] public section

namespace LeanCanny.Computation.SingleCall.Program
open Turing.MultiTapeTM

variable (P : SingleCall.Program) (select : List Bool → Bool) (leaf : List Bool → List Bool)

def withLeaf : SingleCall.Program where
  request p := if select p then false else P.request p
  query := P.query
  immediate p := if select p then leaf p else P.immediate p
  finish := P.finish

theorem withLeaf_value (answer : List Bool → List Bool) (p : List Bool) :
    (P.withLeaf select leaf).value answer p = if select p then leaf p else P.value answer p := by
  cases hs : select p <;> simp only [value, withLeaf, hs, ite_true, Bool.false_eq_true, ite_false]

theorem withLeaf_certificates (hs : (fun p => [select p]) ∈ FP)
    (hr : (fun p => [P.request p]) ∈ FP) (hq : P.query ∈ FP)
    (hi : SpaceFunction P.immediate) (hf : SpaceFunction P.finish) (hL : SpaceFunction leaf) :
    (P.withLeaf select leaf).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) := by
  have hreq := (flag_computable hs).ite' (constFn_mem_FP [false]) hr
  have hreq' : (fun p => [(P.withLeaf select leaf).request p]) ∈ FP := by
    refine mem_FP_of_eq hreq ?_
    intro p
    cases hb : select p <;> simp only [withLeaf, hb, Bool.false_eq_true, ite_false, ite_true]
  have himm := SpaceFunction.branch select hs hL hi
  exact (P.withLeaf select leaf).certificates_of_space hreq' hq himm.computable hf.computable

theorem withLeaf_needs_iterate (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (P.withLeaf select leaf).controller.needs
      ((((P.withLeaf select leaf).controller).reference answer)^[t] (initial p)) =
      if select p then false else P.request p := by
  change (P.withLeaf select leaf).request
    (((((P.withLeaf select leaf).controller).reference answer)^[t] (initial p)).1) = _
  rw [context_iterate]
  rfl

theorem withLeaf_query_iterate (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (P.withLeaf select leaf).controller.query
      ((((P.withLeaf select leaf).controller).reference answer)^[t] (initial p)) = P.query p := by
  change (P.withLeaf select leaf).query
    (((((P.withLeaf select leaf).controller).reference answer)^[t] (initial p)).1) = _
  rw [context_iterate]
  rfl

end LeanCanny.Computation.SingleCall.Program
