/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveControllerSpace

/-! # One guarded task request followed by FP postprocessing

This is the controller used by Berkowitz's diagonal/moment factor selectors.
The answer routine is semantic data; only the request and local processing
receive native computation certificates.
-/

@[expose] public section

namespace LeanCanny.Computation.SingleCall
open Turing.MultiTapeTM

abbrev State := List Bool × Bool × List Bool
abbrev encState : State ↪ List Bool := encPair encBits (encPair encBool encBits)

structure Program where
  request : List Bool → Bool
  query : List Bool → List Bool
  immediate : List Bool → List Bool
  finish : List Bool → List Bool

namespace Program
variable (P : Program)

def initial (p : List Bool) : State := (p, false, [])

def controller : RecursiveController.Controller (List Bool) State where
  initial := initial
  halted := fun s => if s.2.1 then true else !(P.request s.1)
  output := fun s => if s.2.1 then P.finish (pair s.1 s.2.2) else P.immediate s.1
  needs := fun s => P.request s.1
  query := fun s => P.query s.1
  advance := id
  resume := fun p => (p.1.1, true, p.2)

def value (answer : List Bool → List Bool) (p : List Bool) : List Bool :=
  if P.request p then P.finish (pair p (answer (P.query p))) else P.immediate p

theorem reference_initial (answer : List Bool → List Bool) (p : List Bool) :
    P.controller.reference answer (initial p) =
      if P.request p then (p, true, answer (P.query p)) else initial p := by
  cases hr : P.request p <;>
    simp only [RecursiveController.Controller.reference, controller, initial, hr,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, id_eq]

theorem reference_answered (answer : List Bool → List Bool) (p v : List Bool) :
    P.controller.reference answer (p, true, v) = (p, true, v) := rfl

theorem reference_iterate (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (P.controller.reference answer)^[t + 1] (initial p) =
      if P.request p then (p, true, answer (P.query p)) else initial p := by
  induction t with
  | zero => exact P.reference_initial answer p
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    cases hr : P.request p
    · simp only [Bool.false_eq_true, ite_false, P.reference_initial answer p, hr]
    · exact P.reference_answered answer p _

theorem halted_after (answer : List Bool → List Bool) (p : List Bool) :
    P.controller.halted ((P.controller.reference answer)^[1] (initial p)) = true := by
  rw [P.reference_iterate answer p 0]
  cases hr : P.request p <;>
    simp only [hr, Bool.false_eq_true, ite_false, ite_true, controller, initial, Bool.not_false]

theorem context_iterate (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    ((P.controller.reference answer)^[t] (initial p)).1 = p := by
  cases t with
  | zero => rfl
  | succ t => rw [P.reference_iterate]; split_ifs <;> rfl

theorem output_when_halted (answer : List Bool → List Bool) (p : List Bool) (t : ℕ)
    (hh : P.controller.halted ((P.controller.reference answer)^[t] (initial p)) = true) :
    P.controller.output ((P.controller.reference answer)^[t] (initial p)) = P.value answer p := by
  cases t with
  | zero =>
    have hr : P.request p = false := by
      simpa only [Function.iterate_zero, id_eq, controller, initial, Bool.false_eq_true, ite_false,
        Bool.not_eq_true'] using hh
    simp only [Function.iterate_zero, id_eq, controller, initial, value, hr, Bool.false_eq_true, ite_false]
  | succ t =>
    rw [P.reference_iterate]
    cases hr : P.request p <;>
      simp only [hr, Bool.false_eq_true, ite_false, ite_true, controller, initial, value]

theorem state_length (answer : List Bool → List Bool) (p : List Bool) (t : ℕ) :
    (encState ((P.controller.reference answer)^[t] (initial p))).length ≤
      2 * p.length + 4 + (answer (P.query p)).length := by
  cases t with
  | zero => simp only [Function.iterate_zero, id_eq, initial, encState, length_encPair, encBits_apply,
      encBool_apply, List.length_singleton, List.length_nil]; omega
  | succ t =>
    rw [P.reference_iterate]
    split_ifs <;> simp only [initial, encState, length_encPair, encBits_apply,
      encBool_apply, List.length_singleton, List.length_nil] <;> omega

/-- Unused requests impose no answer-size obligation. -/
theorem state_length_of_bound (answer : List Bool → List Bool) (p : List Bool) (t B : ℕ)
    (hb : P.request p = true → (answer (P.query p)).length ≤ B) :
    (encState ((P.controller.reference answer)^[t] (initial p))).length ≤ 2 * p.length + 4 + B := by
  cases t with
  | zero =>
    simp only [Function.iterate_zero, id_eq, initial, encState, length_encPair, encBits_apply,
      encBool_apply, List.length_singleton, List.length_nil]
    omega
  | succ t =>
    rw [P.reference_iterate]
    cases hr : P.request p with
    | false =>
      simp only [Bool.false_eq_true, ite_false, initial, encState, length_encPair, encBits_apply,
        encBool_apply, List.length_singleton, List.length_nil]
      omega
    | true =>
      have hl := hb hr
      simp only [ite_true, encState, length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      omega

structure Controls : Prop where
  request : (fun p => [P.request p]) ∈ FP
  query : P.query ∈ FP
  immediate : P.immediate ∈ FP
  finish : P.finish ∈ FP

/-- Local output processing may use arbitrary polynomial space and time.
Only the request flag and child-task writer are required to be FP. -/
theorem certificates_of_space (hrequest : (fun p => [P.request p]) ∈ FP) (hquery : P.query ∈ FP)
    (himmediate : ComputableTidilyInPolySpace P.immediate encBits encBits)
    (hfinish : ComputableTidilyInPolySpace P.finish encBits encBits) :
    P.controller.Certificates (encQ := encBits) (encS := encState) := by
  have hp : ComputableTidilyInPolyTime (fun s : State => s.1) encState encBits := by fun_prop
  have hb : ComputableTidilyInPolyTime (fun s : State => s.2.1) encState encBool := by fun_prop
  have hr := (flag_computable hrequest).comp hp
  have harg : ComputableTidilyInPolyTime (fun s : State => pair s.1 s.2.2) encState encBits :=
    pair_computable hp (by fun_prop)
  have hi : ComputableTidilyInPolyTime initial encBits encState := by unfold initial; fun_prop
  have hhalt : ComputableTidilyInPolyTime P.controller.halted encState encBool :=
    hb.ite' (ComputableTidilyInPolyTime.const true) ((ComputableTidilyInPolyTime.of_finite Bool.not).comp hr)
  have hout : ComputableTidilyInPolySpace P.controller.output encState encBits :=
    (ComputableTidilyInPolySpace.of_polyTime hb).ite
      (hfinish.comp (ComputableTidilyInPolySpace.of_polyTime harg))
      (himmediate.comp (ComputableTidilyInPolySpace.of_polyTime hp))
  have hresume : ComputableTidilyInPolyTime P.controller.resume (encPair encState encBits) encState := by
    change ComputableTidilyInPolyTime (fun p : State × List Bool => (p.1.1, true, p.2)) _ _
    fun_prop
  exact ⟨.of_polyTime hi, .of_polyTime hhalt, hout, .of_polyTime hr,
    .of_polyTime ((FP.computable hquery).comp hp), .id', .of_polyTime hresume⟩

theorem certificates (h : P.Controls) : P.controller.Certificates (encQ := encBits) (encS := encState) :=
  P.certificates_of_space h.request h.query
    (.of_polyTime (FP.computable h.immediate)) (.of_polyTime (FP.computable h.finish))

end Program
end LeanCanny.Computation.SingleCall
