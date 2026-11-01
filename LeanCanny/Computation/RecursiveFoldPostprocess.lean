/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.RecursiveFoldController
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Context-aware output postprocessing of a native recursive fold -/
@[expose] public section
namespace LeanCanny.Computation.RecursiveFold
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def outputPacket (s : State) : List Bool := pair s.1 s.2.2

theorem outputPacket_space : ComputableTidilyInPolySpace outputPacket encState encBits := by
  unfold outputPacket encState
  fun_prop

def Program.postController (P : Program) (post : List Bool → List Bool) : RecursiveController.Controller (List Bool) State :=
  { P.controller with output := post ∘ outputPacket }

theorem Program.post_certificates (P : Program) (hP : P.controller.Certificates (encQ := encBits) (encS := encState))
    (post : List Bool → List Bool) (hpost : SpaceFunction post) :
    (P.postController post).Certificates (encQ := encBits) (encS := encState) :=
  { hP with output := hpost.computable.comp outputPacket_space }

theorem Program.post_reference (P : Program) (post answer : List Bool → List Bool) :
    (P.postController post).reference answer = P.controller.reference answer := rfl

theorem Program.post_initial (P : Program) (post : List Bool → List Bool) : (P.postController post).initial = P.initial := rfl

theorem Program.post_requests (P : Program) (post answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q c : List Bool) :
    (P.postController post).Requests answer budget q c ↔ P.controller.Requests answer budget q c := Iff.rfl

theorem Program.post_halted_after (P : Program) (post answer : List Bool → List Bool) (q : List Bool) :
    (P.postController post).halted (((P.postController post).reference answer)^[P.count q] ((P.postController post).initial q)) = true :=
  P.halted_after answer q

theorem Program.post_output_when_halted (P : Program) (post answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hh : (P.postController post).halted (((P.postController post).reference answer)^[t] ((P.postController post).initial q)) = true) :
    (P.postController post).output (((P.postController post).reference answer)^[t] ((P.postController post).initial q)) =
      post (pair q (P.value answer q)) := by
  change post (pair (((P.controller.reference answer)^[t] (P.initial q)).1)
    (((P.controller.reference answer)^[t] (P.initial q)).2.2)) = _
  rw [P.reference_iterate]
  have HH : P.count q ≤ min t (P.count q) := by
    rw [post_reference, post_initial, P.reference_iterate] at hh
    exact of_decide_eq_true hh
  rw [show min t (P.count q) = P.count q by omega]
  rfl
end LeanCanny.Computation.RecursiveFold
