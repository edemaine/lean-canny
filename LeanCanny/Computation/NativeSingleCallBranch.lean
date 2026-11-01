/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerBranch
public import LeanCanny.Computation.SingleCallController
public import LeanCanny.Computation.PolyTimePairing
/-! # Native single-call branches include charged local space routines -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open Turing.MultiTapeTM RecursiveController
set_option backward.isDefEq.respectTransparency false

noncomputable def ofSingleCall (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := P.controller
  certificates := hP
  selected := selected
  selected_FP := hs
  model := model
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound q := 2 * q.length + 4 + replyBound q
  stateBound_unary := (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add hb

theorem ofSingleCall_correct (P : SingleCall.Program)
    (hP : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState))
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hv : ∀ q, selected q = true → P.value answer q = model q)
    (hl : ∀ q, selected q = true → P.request q = true → (answer (P.query q)).length ≤ replyBound q)
    (hf : ∀ q child budget, selected q = true → P.controller.Requests answer budget q child → frame q child) :
    Correct (ofSingleCall P hP selected hs model replyBound hb) answer frame where
  halted q _ := P.halted_after answer q
  output q t hq hh := (P.output_when_halted answer q t hh).trans (hv q hq)
  state q t hq := P.state_length_of_bound answer q t (replyBound q) (hl q hq)
  requests := hf

noncomputable def Machine.withGuard (M : Machine) (selected : List Bool → Bool)
    (hs : (fun q => [selected q]) ∈ FP) : Machine := { M with selected := selected, selected_FP := hs }

theorem withGuard_correct (M : Machine) (selected : List Bool → Bool)
    (hs : (fun q => [selected q]) ∈ FP) (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hM : Correct M answer frame) (hi : ∀ q, selected q = true → M.selected q = true) :
    Correct (M.withGuard selected hs) answer frame where
  halted q hq := hM.halted q (hi q hq)
  output q t hq := hM.output q t (hi q hq)
  state q t hq := hM.state q t (hi q hq)
  requests q child budget hq := hM.requests q child budget (hi q hq)

def zeroProgram : SingleCall.Program where
  request _ := false
  query := id
  immediate _ := []
  finish := id

theorem zero_controls : zeroProgram.Controls :=
  ⟨constFn_mem_FP [false], id_mem_FP, constFn_mem_FP [], id_mem_FP⟩

noncomputable def zero : Machine := ofSingleCall zeroProgram (zeroProgram.certificates zero_controls)
  (fun _ => true) (constFn_mem_FP [true]) (fun _ => []) (fun _ => 0) (UnaryFn.const 0)

theorem zero_correct (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop) : Correct zero answer frame := by
  apply ofSingleCall_correct
  · intro q _
    rfl
  · intro q _ h
    cases h
  · intro q child budget _ h
    obtain ⟨hr, _⟩ := (zeroProgram.requests_iff answer budget q child).mp h
    cases hr

end LeanCanny.Computation.NativeControllerBranch
