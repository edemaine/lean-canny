/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeControllerBranch
public import Mathlib.Data.List.Nodup
/-! # Selected models in native dispatchers with distinct phase codes -/
@[expose] public section
namespace LeanCanny.Computation.NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

structure PhaseNode (phaseCode : List Bool → ℕ) where
  machine : Machine
  code : ℕ
  selected_phase : ∀ q, machine.selected q = true → phaseCode q = code

noncomputable def phaseDispatch {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine) : Machine :=
  nodes.foldr (fun b n => b.machine.choose n) fallback

theorem phaseDispatch_correct {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hf : Correct fallback answer frame) (hn : ∀ b ∈ nodes, Correct b.machine answer frame) :
    Correct (phaseDispatch nodes fallback) answer frame := by
  revert hn
  induction nodes with
  | nil => intro _; exact hf
  | cons b bs ih =>
    intro hn
    exact choose_correct _ _ answer frame (hn b List.mem_cons_self)
      (ih (fun c hc => hn c (List.mem_cons_of_mem _ hc)))

theorem phaseDispatch_model_none {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine)
    (q : List Bool) (hn : ∀ b ∈ nodes, b.machine.selected q = false) :
    (phaseDispatch nodes fallback).model q = fallback.model q := by
  revert hn
  induction nodes with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro hn
    change (if b.machine.selected q then b.machine.model q else (phaseDispatch bs fallback).model q) = _
    rw [hn b List.mem_cons_self]
    exact ih (fun c hc => hn c (List.mem_cons_of_mem _ hc))

theorem phaseDispatch_model_selected {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine)
    (q : List Bool) (b : PhaseNode phaseCode) (hn : (nodes.map PhaseNode.code).Nodup)
    (hb : b ∈ nodes) (hs : b.machine.selected q = true) :
    (phaseDispatch nodes fallback).model q = b.machine.model q := by
  revert hn hb
  induction nodes with
  | nil => intro _ hb; cases hb
  | cons c cs ih =>
    intro hn hb
    have HN := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hb with HE | HB
    · subst b
      change (if c.machine.selected q then c.machine.model q else (phaseDispatch cs fallback).model q) = _
      rw [hs, ite_eq_left rfl]
    · have HC : c.code ≠ b.code := by
        intro HE
        exact HN.1 (List.mem_map.mpr ⟨b, HB, HE.symm⟩)
      have HF : c.machine.selected q = false := by
        cases ht : c.machine.selected q with
        | false => rfl
        | true => exact False.elim (HC ((c.selected_phase q ht).symm.trans (b.selected_phase q hs)))
      change (if c.machine.selected q then c.machine.model q else (phaseDispatch cs fallback).model q) = _
      rw [HF]
      exact ih HN.2 HB

theorem phaseDispatch_model_off {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine)
    (q : List Bool) (hn : phaseCode q ∉ nodes.map PhaseNode.code) :
    (phaseDispatch nodes fallback).model q = fallback.model q := by
  apply phaseDispatch_model_none
  intro b hb
  cases hs : b.machine.selected q with
  | false => rfl
  | true => exact False.elim (hn (List.mem_map.mpr ⟨b, hb, (b.selected_phase q hs).symm⟩))

theorem phaseDispatch_model_at_code {phaseCode : List Bool → ℕ} (nodes : List (PhaseNode phaseCode)) (fallback : Machine)
    (q : List Bool) (b : PhaseNode phaseCode) (hn : (nodes.map PhaseNode.code).Nodup)
    (hb : b ∈ nodes) (hp : phaseCode q = b.code) :
    (phaseDispatch nodes fallback).model q = if b.machine.selected q then b.machine.model q else fallback.model q := by
  by_cases hs : b.machine.selected q = true
  · rw [ite_eq_left hs]
    exact phaseDispatch_model_selected nodes fallback q b hn hb hs
  · rw [ite_eq_right hs]
    apply phaseDispatch_model_none
    intro c hc
    cases ht : c.machine.selected q with
    | false => rfl
    | true =>
      have HE : c = b := List.inj_on_of_nodup_map hn hc hb ((c.selected_phase q ht).symm.trans hp)
      exact False.elim (hs (HE ▸ ht))

end LeanCanny.Computation.NativeControllerBranch
