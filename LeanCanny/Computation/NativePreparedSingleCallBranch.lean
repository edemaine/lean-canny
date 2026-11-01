/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Prepared native single-call stages keep only their local input packet -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open Turing.MultiTapeTM RecursiveController
set_option backward.isDefEq.respectTransparency false

noncomputable def ofPreparedSingleCall (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (input : List Bool → List Bool) (hi : input ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := P.controller.prepare input
  certificates := Controller.prepare_certificates P.controller input hP (FP.computable hi)
  selected := selected
  selected_FP := hs
  model := model
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound q := 2 * (input q).length + 4 + replyBound q
  stateBound_unary := (((UnaryFn.const 2).mul (UnaryFn.length hi)).add (UnaryFn.const 4)).add hb

theorem ofPreparedSingleCall_correct (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (input : List Bool → List Bool) (hi : input ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hv : ∀ q, selected q = true → P.value answer (input q) = model q)
    (hl : ∀ q, selected q = true → P.request (input q) = true → (answer (P.query (input q))).length ≤ replyBound q)
    (hf : ∀ q child budget, selected q = true → (P.controller.prepare input).Requests answer budget q child → frame q child) :
    Correct (ofPreparedSingleCall P hP input hi selected hs model replyBound hb) answer frame := by
  constructor
  · intro q _
    exact P.halted_after answer (input q)
  · intro q t hq hh
    exact (P.output_when_halted answer (input q) t hh).trans (hv q hq)
  · intro q t hq
    exact P.state_length_of_bound answer (input q) t (replyBound q) (hl q hq)
  · exact hf

end LeanCanny.Computation.NativeControllerBranch
