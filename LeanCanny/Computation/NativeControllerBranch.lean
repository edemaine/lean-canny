/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # Native controller branches with local clocks and encoded-state bounds -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
open Turing.MultiTapeTM RecursiveController
set_option backward.isDefEq.respectTransparency false

structure Machine where
  State : Type
  defaultValue : State
  encoding : State ↪ List Bool
  controller : Controller (List Bool) State
  certificates : controller.Certificates (encQ := encBits) (encS := encoding)
  selected : List Bool → Bool
  selected_FP : (fun q => [selected q]) ∈ FP
  model : List Bool → List Bool
  clock : List Bool → ℕ
  clock_binary : BinaryFn clock
  stateBound : List Bool → ℕ
  stateBound_unary : UnaryFn stateBound

noncomputable def Machine.choose (M N : Machine) : Machine := by
  letI : Inhabited M.State := ⟨M.defaultValue⟩
  letI : Inhabited N.State := ⟨N.defaultValue⟩
  let HM := FPPred.of_flag M.selected_FP
  let HN := FPPred.of_flag N.selected_FP
  exact {
    State := Controller.ChoiceState M.State N.State
    defaultValue := (false, M.defaultValue, N.defaultValue)
    encoding := Controller.encChoice M.encoding N.encoding
    controller := Controller.choose M.selected M.controller N.controller
    certificates := Controller.choose_certificates _ _ _ (flag_computable M.selected_FP) M.certificates N.certificates
    selected q := M.selected q || N.selected q
    selected_FP := mem_FP_of_eq (HM.or HN).flag_mem_FP (fun q => by cases M.selected q <;> cases N.selected q <;> rfl)
    model q := if M.selected q then M.model q else N.model q
    clock q := if M.selected q then M.clock q else N.clock q
    clock_binary := BinaryFn.ite HM M.clock_binary N.clock_binary
    stateBound q := 4 + 2 * (if M.selected q then M.stateBound q else N.stateBound q) +
      2 * (M.encoding M.defaultValue).length + (N.encoding N.defaultValue).length
    stateBound_unary := (((UnaryFn.const 4).add ((UnaryFn.const 2).mul
      (UnaryFn.ite HM M.stateBound_unary N.stateBound_unary))).add
        (UnaryFn.const (2 * (M.encoding M.defaultValue).length))).add
        (UnaryFn.const (N.encoding N.defaultValue).length) }

structure Correct (M : Machine) (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop) : Prop where
  halted : ∀ q, M.selected q = true →
    M.controller.halted ((M.controller.reference answer)^[M.clock q] (M.controller.initial q)) = true
  output : ∀ q t, M.selected q = true →
    M.controller.halted ((M.controller.reference answer)^[t] (M.controller.initial q)) = true →
    M.controller.output ((M.controller.reference answer)^[t] (M.controller.initial q)) = M.model q
  state : ∀ q t, M.selected q = true →
    (M.encoding ((M.controller.reference answer)^[t] (M.controller.initial q))).length ≤ M.stateBound q
  requests : ∀ q child budget, M.selected q = true → M.controller.Requests answer budget q child → frame q child

theorem choose_correct (M N : Machine) (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hM : Correct M answer frame) (hN : Correct N answer frame) : Correct (M.choose N) answer frame := by
  let : Inhabited M.State := ⟨M.defaultValue⟩
  let : Inhabited N.State := ⟨N.defaultValue⟩
  have HN (q : List Bool) (h : (M.choose N).selected q = true) (hm : M.selected q = false) : N.selected q = true := by
    change (M.selected q || N.selected q) = true at h
    simpa only [hm, Bool.false_or] using h
  constructor
  · intro q hq
    change (Controller.choose M.selected M.controller N.controller).halted
      (((Controller.choose M.selected M.controller N.controller).reference answer)^[if M.selected q then M.clock q else N.clock q]
        ((Controller.choose M.selected M.controller N.controller).initial q)) = true
    rw [Controller.choose_halted_iterate]
    cases hm : M.selected q with
    | true => simpa only [hm, ite_true] using hM.halted q hm
    | false => simpa only [hm, Bool.false_eq_true, ite_false] using hN.halted q (HN q hq hm)
  · intro q t hq hh
    change (Controller.choose M.selected M.controller N.controller).halted
      (((Controller.choose M.selected M.controller N.controller).reference answer)^[t]
        ((Controller.choose M.selected M.controller N.controller).initial q)) = true at hh
    change (Controller.choose M.selected M.controller N.controller).output
      (((Controller.choose M.selected M.controller N.controller).reference answer)^[t]
        ((Controller.choose M.selected M.controller N.controller).initial q)) =
      if M.selected q then M.model q else N.model q
    rw [Controller.choose_halted_iterate] at hh
    rw [Controller.choose_output_iterate]
    cases hm : M.selected q with
    | true => simpa only [hm, ite_true] using hM.output q t hm (by simpa only [hm, ite_true] using hh)
    | false =>
      simpa only [hm, Bool.false_eq_true, ite_false] using hN.output q t (HN q hq hm)
        (by simpa only [hm, Bool.false_eq_true, ite_false] using hh)
  · intro q t hq
    change (Controller.encChoice M.encoding N.encoding
      (((Controller.choose M.selected M.controller N.controller).reference answer)^[t]
        ((Controller.choose M.selected M.controller N.controller).initial q))).length ≤ _
    apply Controller.choose_state_length M.selected M.controller N.controller M.encoding N.encoding answer q t
      (if M.selected q then M.stateBound q else N.stateBound q)
    · intro hm
      simpa only [hm, ite_true] using hM.state q t hm
    · intro hm
      simpa only [hm, Bool.false_eq_true, ite_false] using hN.state q t (HN q hq hm)
  · intro q child budget hq hr
    change (Controller.choose M.selected M.controller N.controller).Requests answer budget q child at hr
    rw [Controller.choose_requests_iff] at hr
    cases hm : M.selected q with
    | true => exact hM.requests q child budget hm (by simpa only [hm, ite_true] using hr)
    | false => exact hN.requests q child budget (HN q hq hm) (by simpa only [hm, Bool.false_eq_true, ite_false] using hr)

end LeanCanny.Computation.NativeControllerBranch
