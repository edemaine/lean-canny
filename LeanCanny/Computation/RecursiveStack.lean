/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-! # A uniform call stack for recursive space computations

An action finishes a frame, continues locally, or starts a child frame while
saving its caller. Replies are installed by one fixed receive operation.
The semantic frame value and progress measures below are proof data only.
-/

@[expose] public section

namespace LeanCanny.Computation.RecursiveStack

abbrev Action (F : Type) := Bool × Bool × List Bool × F
abbrev State (F : Type) := Bool × List Bool × F × List F

def Action.done {F : Type} (s : F) (a : List Bool) : Action F := (true, false, a, s)
def Action.next {F : Type} (s : F) : Action F := (false, false, [], s)
def Action.call {F : Type} (s : F) : Action F := (false, true, [], s)

def initial {F : Type} (s : F) : State F := (false, [], s, [])

def step {F : Type} (localStep : F → Action F) (receive : F × List Bool → F) (s : State F) : State F :=
  if s.1 then s else
    let a := localStep s.2.2.1
    if a.1 then
      match s.2.2.2 with
      | [] => (true, a.2.2.1, s.2.2.1, [])
      | parent :: rest => (false, [], receive (parent, a.2.2.1), rest)
    else if a.2.1 then (false, [], a.2.2.2, s.2.2.1 :: s.2.2.2)
    else (false, [], a.2.2.2, s.2.2.2)

def finish {F : Type} (receive : F × List Bool → F) (value : F → List Bool) : List F → List Bool → List Bool
  | [], a => a
  | parent :: rest, a => finish receive value rest (value (receive (parent, a)))

def denote {F : Type} (receive : F × List Bool → F) (value : F → List Bool) (s : State F) : List Bool :=
  if s.1 then s.2.1 else finish receive value s.2.2.2 (value s.2.2.1)

structure Rules {F : Type} (localStep : F → Action F) (receive : F × List Bool → F)
    (value : F → List Bool) (rank fuel : F → ℕ) (valid : F → Prop) (N : ℕ) : Prop where
  bound : ∀ s, valid s → fuel s ≤ N
  done : ∀ s, valid s → (localStep s).1 = true → (localStep s).2.2.1 = value s
  next : ∀ s, valid s → (localStep s).1 = false → (localStep s).2.1 = false →
    valid (localStep s).2.2.2 ∧ rank (localStep s).2.2.2 ≤ rank s ∧
    fuel (localStep s).2.2.2 < fuel s ∧ value (localStep s).2.2.2 = value s
  call : ∀ s, valid s → (localStep s).1 = false → (localStep s).2.1 = true →
    valid (localStep s).2.2.2 ∧ rank (localStep s).2.2.2 < rank s ∧
    valid (receive (s, value (localStep s).2.2.2)) ∧ rank (receive (s, value (localStep s).2.2.2)) ≤ rank s ∧
    fuel (receive (s, value (localStep s).2.2.2)) < fuel s ∧
    value (receive (s, value (localStep s).2.2.2)) = value s

def Chain {F : Type} (localStep : F → Action F) (value : F → List Bool) (rank : F → ℕ)
    (valid : F → Prop) : List Bool → ℕ → List F → Prop
  | _, _, [] => True
  | a, r, parent :: rest => valid parent ∧ (localStep parent).1 = false ∧ (localStep parent).2.1 = true ∧
      a = value (localStep parent).2.2.2 ∧ r < rank parent ∧
      Chain localStep value rank valid (value parent) (rank parent) rest

theorem Chain.lower {F : Type} {localStep : F → Action F} {value : F → List Bool} {rank : F → ℕ} {valid : F → Prop}
    {a : List Bool} {r t : ℕ} {stack : List F} (h : Chain localStep value rank valid a r stack) (ht : t ≤ r) :
    Chain localStep value rank valid a t stack := by
  cases stack with
  | nil => trivial
  | cons parent rest => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, lt_of_le_of_lt ht h.2.2.2.2.1, h.2.2.2.2.2⟩

def Good {F : Type} (localStep : F → Action F) (value : F → List Bool) (rank : F → ℕ)
    (valid : F → Prop) (s : State F) : Prop :=
  valid s.2.2.1 ∧ (if s.1 then s.2.2.2 = [] else Chain localStep value rank valid (value s.2.2.1) (rank s.2.2.1) s.2.2.2)

theorem good_initial {F : Type} (localStep : F → Action F) (value : F → List Bool) (rank : F → ℕ)
    (valid : F → Prop) (s : F) (hs : valid s) : Good localStep value rank valid (initial s) := ⟨hs, trivial⟩

theorem good_step {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) : Good localStep value rank valid (step localStep receive s) := by
  rcases s with ⟨halted, output, current, stack⟩
  cases halted with
  | true => simpa only [step, ite_true] using hs
  | false =>
    have hv : valid current := hs.1
    have hc : Chain localStep value rank valid (value current) (rank current) stack := hs.2
    by_cases hd : (localStep current).1 = true
    · have ha := rules.done current hv hd
      cases stack with
      | nil =>
        simp only [step, Bool.false_eq_true, ite_false, ite_eq_left hd]
        exact ⟨hv, rfl⟩
      | cons parent rest =>
        have hr := rules.call parent hc.1 hc.2.1 hc.2.2.1
        have he : (localStep current).2.2.1 = value (localStep parent).2.2.2 := ha.trans hc.2.2.2.1
        simp only [step, Bool.false_eq_true, ite_false, ite_eq_left hd, he]
        exact ⟨hr.2.2.1, by rw [hr.2.2.2.2.2]; exact hc.2.2.2.2.2.lower hr.2.2.2.1⟩
    · have hd' : (localStep current).1 = false := Bool.eq_false_iff.mpr hd
      by_cases hcall : (localStep current).2.1 = true
      · have hr := rules.call current hv hd' hcall
        simp only [step, Bool.false_eq_true, ite_false, hd', hcall, ite_true]
        exact ⟨hr.1, hv, hd', hcall, rfl, hr.2.1, hc⟩
      · have hcall' : (localStep current).2.1 = false := Bool.eq_false_iff.mpr hcall
        have hr := rules.next current hv hd' hcall'
        simp only [step, Bool.false_eq_true, ite_false, hd', hcall', ite_false]
        exact ⟨hr.1, by rw [hr.2.2.2]; exact hc.lower hr.2.1⟩

theorem denote_step {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) : denote receive value (step localStep receive s) = denote receive value s := by
  rcases s with ⟨halted, output, current, stack⟩
  cases halted with
  | true => rfl
  | false =>
    have hv : valid current := hs.1
    by_cases hd : (localStep current).1 = true
    · have ha := rules.done current hv hd
      cases stack <;> simp only [step, Bool.false_eq_true, ite_false, ite_eq_left hd, denote, ite_true, finish, ha]
    · have hd' : (localStep current).1 = false := Bool.eq_false_iff.mpr hd
      by_cases hcall : (localStep current).2.1 = true
      · have hr := rules.call current hv hd' hcall
        simp only [step, hd', hcall, denote, Bool.false_eq_true, ite_false, ite_true, finish, hr.2.2.2.2.2]
      · have hcall' : (localStep current).2.1 = false := Bool.eq_false_iff.mpr hcall
        have hr := rules.next current hv hd' hcall'
        simp only [step, hd', hcall', denote, Bool.false_eq_true, ite_false, hr.2.2.2]

theorem good_iterate {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (k : ℕ) :
    Good localStep value rank valid ((step localStep receive)^[k] s) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact good_step rules _ ih

theorem denote_iterate {F : Type} {localStep : F → Action F} {receive : F × List Bool → F}
    {value : F → List Bool} {rank fuel : F → ℕ} {valid : F → Prop} {N : ℕ}
    (rules : Rules localStep receive value rank fuel valid N) (s : State F)
    (hs : Good localStep value rank valid s) (k : ℕ) :
    denote receive value ((step localStep receive)^[k] s) = denote receive value s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (denote_step rules _ (good_iterate rules s hs k)).trans ih

end LeanCanny.Computation.RecursiveStack
