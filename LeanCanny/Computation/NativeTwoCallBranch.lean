/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerBranch
public import LeanCanny.Computation.DependentTwoCallController
/-! # Native adaptive two-call branches with explicit retained-reply bounds -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def ofTwoCalls (left right post : List Bool → List Bool)
    (hl : left ∈ FP) (hr : right ∈ FP) (hp : post ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := DependentTwoCall.controller left right post
  certificates := DependentTwoCall.certificates left right post hl hr hp
  selected := selected
  selected_FP := hs
  model := model
  clock _ := 2
  clock_binary := BinaryFn.const 2
  stateBound q := 2 * q.length + 2 * (encNat 2).length + replyBound q + 2
  stateBound_unary := ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add
    (UnaryFn.const (2 * (encNat 2).length))).add hb).add (UnaryFn.const 2)

theorem ofTwoCalls_correct (left right post : List Bool → List Bool)
    (hl : left ∈ FP) (hr : right ∈ FP) (hp : post ∈ FP)
    (selected : List Bool → Bool) (hs : (fun q => [selected q]) ∈ FP)
    (model : List Bool → List Bool) (replyBound : List Bool → ℕ) (hb : UnaryFn replyBound)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hv : ∀ q, selected q = true → DependentTwoCall.result left right post answer q = model q)
    (hleft : ∀ q, selected q = true → (answer (left q)).length ≤ replyBound q)
    (houtput : ∀ q, selected q = true → (model q).length ≤ replyBound q)
    (hf : ∀ q child budget, selected q = true →
      (DependentTwoCall.controller left right post).Requests answer budget q child → frame q child) :
    Correct (ofTwoCalls left right post hl hr hp selected hs model replyBound hb) answer frame where
  halted q _ := DependentTwoCall.halted_after left right post answer q
  output q t hq hh := (DependentTwoCall.output_when_halted left right post answer q t hh).trans (hv q hq)
  state q t hq := by
    have H := DependentTwoCall.state_length left right post answer q t
    rw [hv q hq] at H
    change _ ≤ 2 * q.length + 2 * (encNat 2).length + replyBound q + 2
    exact H.trans (by have HL := hleft q hq; have HO := houtput q hq; omega)
  requests := hf

end LeanCanny.Computation.NativeControllerBranch
