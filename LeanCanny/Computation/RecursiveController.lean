/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.HaltingDistance

/-! # Recursive calls from resumable streamed controllers

Frames store a task and its controller state. A source request initializes a
lower-rank task; its answer is installed in the suspended controller. Valid
states are prefixes of the mathematical oracle run, with no stored clock.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveController
open RecursiveStack

structure Controller (Q S : Type) where
  initial : Q → S
  halted : S → Bool
  output : S → List Bool
  needs : S → Bool
  query : S → Q
  advance : S → S
  resume : S × List Bool → S

abbrev Frame (Q S : Type) := Q × S

namespace Controller
variable {Q S : Type} (C : Controller Q S)

def reference (answer : Q → List Bool) (s : S) : S :=
  if C.halted s then s else if C.needs s then C.resume (s, answer (C.query s)) else C.advance s

def instruction (f : Frame Q S) : Action (Frame Q S) :=
  if C.halted f.2 then Action.done f (C.output f.2)
  else if C.needs f.2 then Action.call (C.query f.2, C.initial (C.query f.2))
  else Action.next (f.1, C.advance f.2)

def receive (p : Frame Q S × List Bool) : Frame Q S :=
  (p.1.1, C.resume (p.1.2, p.2))

def Valid (answer : Q → List Bool) (tasks : Q → Prop) (budget : Q → ℕ) (f : Frame Q S) : Prop :=
  tasks f.1 ∧ ∃ t ≤ budget f.1, f.2 = (C.reference answer)^[t] (C.initial f.1)

theorem valid_initial (answer : Q → List Bool) (tasks : Q → Prop) (budget : Q → ℕ)
    (q : Q) (hq : tasks q) : C.Valid answer tasks budget (q, C.initial q) :=
  ⟨hq, 0, Nat.zero_le _, rfl⟩

theorem valid_reference {answer : Q → List Bool} {tasks : Q → Prop} {budget : Q → ℕ}
    (hstop : ∀ q, tasks q → C.halted ((C.reference answer)^[budget q] (C.initial q)) = true)
    (f : Frame Q S) (hf : C.Valid answer tasks budget f) (hh : C.halted f.2 = false) :
    C.Valid answer tasks budget (f.1, C.reference answer f.2) := by
  obtain ⟨hq, t, ht, he⟩ := hf
  have hl : t < budget f.1 := by
    by_contra hn
    have ht' : t = budget f.1 := by omega
    have hs := hstop f.1 hq
    rw [← ht', ← he, hh] at hs
    contradiction
  refine ⟨hq, t + 1, ?_, ?_⟩
  · change t + 1 ≤ budget f.1
    omega
  rw [Function.iterate_succ_apply', ← he]

theorem fuel_bound {answer : Q → List Bool} {tasks : Q → Prop} {budget : Q → ℕ} {N : ℕ}
    (hstop : ∀ q, tasks q → C.halted ((C.reference answer)^[budget q] (C.initial q)) = true)
    (hb : ∀ q, tasks q → budget q ≤ N) (f : Frame Q S) (hf : C.Valid answer tasks budget f) :
    HaltingDistance.remaining (C.reference answer) C.halted f.2 ≤ N := by
  obtain ⟨hq, t, ht, he⟩ := hf
  have hh := HaltingDistance.suffix (C.reference answer) C.halted (C.initial f.1)
    (budget f.1) t (hstop f.1 hq) ht
  rw [← he] at hh
  exact (HaltingDistance.le _ _ _ _ hh).trans ((Nat.sub_le _ _).trans (hb _ hq))

private theorem local_done (f : Frame Q S) : (C.instruction f).1 = C.halted f.2 := by
  cases hh : C.halted f.2 <;> cases hn : C.needs f.2 <;>
    simp only [instruction, hh, hn, Bool.false_eq_true, ite_false, ite_true, Action.done, Action.call, Action.next]

private theorem local_call (f : Frame Q S) (hh : C.halted f.2 = false) :
    (C.instruction f).2.1 = C.needs f.2 := by
  cases hn : C.needs f.2 <;>
    simp only [instruction, hh, hn, Bool.false_eq_true, ite_false, ite_true, Action.call, Action.next]

theorem rules (answer : Q → List Bool) (rank : Q → ℕ) (tasks : Q → Prop) (budget : Q → ℕ) (N : ℕ)
    (hstop : ∀ q, tasks q → C.halted ((C.reference answer)^[budget q] (C.initial q)) = true)
    (hb : ∀ q, tasks q → budget q ≤ N)
    (hdone : ∀ f, C.Valid answer tasks budget f → C.halted f.2 = true → C.output f.2 = answer f.1)
    (hquery : ∀ f, C.Valid answer tasks budget f → C.halted f.2 = false → C.needs f.2 = true →
      tasks (C.query f.2) ∧ rank (C.query f.2) < rank f.1) :
    Rules C.instruction C.receive (fun f => answer f.1) (fun f => rank f.1)
      (fun f => HaltingDistance.remaining (C.reference answer) C.halted f.2)
      (C.Valid answer tasks budget) N := by
  have hprogress (f : Frame Q S) (hf : C.Valid answer tasks budget f) (hh : C.halted f.2 = false) :
      HaltingDistance.remaining (C.reference answer) C.halted (C.reference answer f.2) <
        HaltingDistance.remaining (C.reference answer) C.halted f.2 := by
    obtain ⟨hq, t, ht, he⟩ := hf
    have hs := HaltingDistance.suffix (C.reference answer) C.halted (C.initial f.1)
      (budget f.1) t (hstop f.1 hq) ht
    rw [← he] at hs
    exact HaltingDistance.decreases _ _ _ ⟨_, hs⟩ hh
  constructor
  · exact C.fuel_bound hstop hb
  · intro f hf hd
    have hh : C.halted f.2 = true := (C.local_done f).symm.trans hd
    simpa only [instruction, hh, ite_true, Action.done] using hdone f hf hh
  · intro f hf hd hc
    have hh : C.halted f.2 = false := (C.local_done f).symm.trans hd
    have hn : C.needs f.2 = false := (C.local_call f hh).symm.trans hc
    have he : C.reference answer f.2 = C.advance f.2 := by
      simp only [reference, hh, hn, Bool.false_eq_true, ite_false]
    have hv := C.valid_reference hstop f hf hh
    have hp := hprogress f hf hh
    rw [he] at hv hp
    simpa only [instruction, hh, hn, Bool.false_eq_true, ite_false, Action.next] using
      (show C.Valid answer tasks budget (f.1, C.advance f.2) ∧ rank f.1 ≤ rank f.1 ∧
        HaltingDistance.remaining (C.reference answer) C.halted (C.advance f.2) <
          HaltingDistance.remaining (C.reference answer) C.halted f.2 ∧ answer f.1 = answer f.1 from
        ⟨hv, le_rfl, hp, rfl⟩)
  · intro f hf hd hc
    have hh : C.halted f.2 = false := (C.local_done f).symm.trans hd
    have hn : C.needs f.2 = true := (C.local_call f hh).symm.trans hc
    have hq := hquery f hf hh hn
    have he : C.reference answer f.2 = C.resume (f.2, answer (C.query f.2)) := by
      simp only [reference, hh, hn, Bool.false_eq_true, ite_false, ite_true]
    have hv := C.valid_reference hstop f hf hh
    have hp := hprogress f hf hh
    rw [he] at hv hp
    simpa only [instruction, hh, hn, Bool.false_eq_true, ite_false, ite_true, Action.call, receive] using
      (show C.Valid answer tasks budget (C.query f.2, C.initial (C.query f.2)) ∧
        rank (C.query f.2) < rank f.1 ∧ C.Valid answer tasks budget (f.1, C.resume (f.2, answer (C.query f.2))) ∧
        rank f.1 ≤ rank f.1 ∧
        HaltingDistance.remaining (C.reference answer) C.halted (C.resume (f.2, answer (C.query f.2))) <
          HaltingDistance.remaining (C.reference answer) C.halted f.2 ∧ answer f.1 = answer f.1 from
        ⟨C.valid_initial answer tasks budget _ hq.1, hq.2, hv, le_rfl, hp, rfl⟩)

end Controller
end LeanCanny.Computation.RecursiveController
