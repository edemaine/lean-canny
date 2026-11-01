/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ControllerRequests

/-! # Native input retargeting for one-request controllers

Only the local controller context is retargeted. The emitted task is still
written by the original program, so no nested context is stored in a child.
-/

@[expose] public section
namespace LeanCanny.Computation.SingleCall.Program
set_option backward.isDefEq.respectTransparency false

def requery (P : Program) (f : List Bool → List Bool) : Program where
  request := P.request ∘ f
  query := P.query ∘ f
  immediate := P.immediate ∘ f
  finish z := P.finish (pair (f (pairFst z)) (pairSnd z))

theorem requery_controls (P : Program) (h : P.Controls) (f : List Bool → List Bool) (hf : f ∈ FP) :
    (P.requery f).Controls where
  request := mem_FP_comp (f := f) (g := fun p => [P.request p]) hf h.request
  query := mem_FP_comp (f := f) (g := P.query) hf h.query
  immediate := mem_FP_comp (f := f) (g := P.immediate) hf h.immediate
  finish := mem_FP_comp (g := P.finish) (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP) h.finish

theorem requery_value (P : Program) (f answer : List Bool → List Bool) (q : List Bool) :
    (P.requery f).value answer q = P.value answer (f q) := by
  simp only [value, requery, Function.comp_apply, pairFst_pair, pairSnd_pair]

theorem requery_requests_iff (P : Program) (f answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q child : List Bool) :
    (P.requery f).controller.Requests answer budget q child ↔
      P.request (f q) = true ∧ child = P.query (f q) := by
  rw [requests_iff]
  rfl

end LeanCanny.Computation.SingleCall.Program
