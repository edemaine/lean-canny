/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerBranch
/-! # Preparing an arbitrary native controller preserves its local bounds

Only the initial packet changes. Recursive answers and child packets remain
in the original task space, so the caller supplies the conditional frame
transport from the prepared parent back to its original parent.
-/
@[expose] public section
namespace LeanCanny.Computation.NativePreparedBranch
open Turing.MultiTapeTM RecursiveController NativeControllerBranch

noncomputable def machine (M : Machine) (input : List Bool → List Bool) (hi : input ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) : Machine where
  State := M.State
  defaultValue := M.defaultValue
  encoding := M.encoding
  controller := M.controller.prepare input
  certificates := Controller.prepare_certificates M.controller input M.certificates (FP.computable hi)
  selected := selected
  selected_FP := hs
  model := model
  clock q := M.clock (input q)
  clock_binary := M.clock_binary.comp hi
  stateBound q := M.stateBound (input q)
  stateBound_unary := M.stateBound_unary.comp hi

theorem correct (M : Machine) (input : List Bool → List Bool) (hi : input ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hm : Correct M answer frame)
    (hselected : ∀ q, selected q=true → M.selected (input q)=true)
    (hmodel : ∀ q, selected q=true → M.model (input q)=model q)
    (hframe : ∀ q child, selected q=true → frame (input q) child → frame q child) :
    Correct (machine M input hi selected hs model) answer frame := by
  constructor
  · intro q hq
    exact hm.halted (input q) (hselected q hq)
  · intro q t hq hh
    exact (hm.output (input q) t (hselected q hq) hh).trans (hmodel q hq)
  · intro q t hq
    exact hm.state (input q) t (hselected q hq)
  · intro q child budget hq hc
    have H := (Controller.prepare_requests_iff M.controller input answer budget q child).mp hc
    exact hframe q child hq (hm.requests (input q) child (fun _ => budget q) (hselected q hq) H)

end LeanCanny.Computation.NativePreparedBranch
