/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermCircuit

/-! # Sequential source-circuit compilation

The traversal shares one fresh-wire counter across both children. Its value
stack stores wire indices, and the accumulator stores only primitive gates.
The bounded execution agrees exactly with the recursively defined circuit.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source.Machine

inductive Instruction where
  | visit (t : Term)
  | join (multiply : Bool)
  deriving DecidableEq, Repr

structure State where
  todo : List Instruction
  values : List ℕ
  next : ℕ
  result : List Gate
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.todo with
  | [] => s
  | .visit (.const z) :: rest =>
      ⟨rest, s.next :: s.values, s.next + 1, s.result ++ [.constant s.next z]⟩
  | .visit (.var i) :: rest => ⟨rest, i :: s.values, s.next, s.result⟩
  | .visit (.add a b) :: rest => ⟨.visit a :: .visit b :: .join false :: rest, s.values, s.next, s.result⟩
  | .visit (.mul a b) :: rest => ⟨.visit a :: .visit b :: .join true :: rest, s.values, s.next, s.result⟩
  | .join multiply :: rest =>
      match s.values with
      | right :: left :: values =>
          ⟨rest, s.next :: values, s.next + 1,
            s.result ++ [if multiply then .mul s.next left right else .add s.next left right]⟩
      | _ => s

def work : Term → ℕ
  | .const _ | .var _ => 1
  | .add a b | .mul a b => work a + work b + 2

theorem work_le_dataSize (t : Term) : work t ≤ 2 * t.toData.size := by
  induction t with
  | const z => have h := @Data.size_pos (Term.const z).toData; simp only [work]; omega
  | var i => have h := @Data.size_pos (Term.var i).toData; simp only [work]; omega
  | add a b ha hb => simp only [work, Term.dataSize_add]; omega
  | mul a b ha hb => simp only [work, Term.dataSize_mul]; omega

theorem visit_steps (t : Term) (todo : List Instruction) (values : List ℕ)
    (start : ℕ) (prior : List Gate) :
    step^[work t] ⟨.visit t :: todo, values, start, prior⟩ =
      ⟨todo, output start t :: values, start + count t, prior ++ gates start t⟩ := by
  induction t generalizing todo values start prior with
  | const z => rfl
  | var i => simp [work, step, output, count, gates]
  | add a b ha hb =>
    rw [work, show work a + work b + 2 = (1 + work b + work a) + 1 by omega,
      Function.iterate_succ_apply]
    change step^[1 + work b + work a]
      ⟨.visit a :: .visit b :: .join false :: todo, values, start, prior⟩ = _
    rw [Function.iterate_add_apply step (1 + work b) (work a), ha,
      Function.iterate_add_apply step 1 (work b), hb]
    simp only [Function.iterate_one, step, Bool.false_eq_true, ite_false, output, count, gates, List.append_assoc]
    congr 1; omega
  | mul a b ha hb =>
    rw [work, show work a + work b + 2 = (1 + work b + work a) + 1 by omega,
      Function.iterate_succ_apply]
    change step^[1 + work b + work a]
      ⟨.visit a :: .visit b :: .join true :: todo, values, start, prior⟩ = _
    rw [Function.iterate_add_apply step (1 + work b) (work a), ha,
      Function.iterate_add_apply step 1 (work b), hb]
    simp only [Function.iterate_one, step, ite_true, output, count, gates, List.append_assoc]
    congr 1; omega

theorem run_steps (t : Term) (start fuel : ℕ) (hfuel : work t ≤ fuel) :
    step^[fuel] ⟨[.visit t], [], start, []⟩ =
      ⟨[], [output start t], start + count t, gates start t⟩ := by
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hfuel
  rw [he, Nat.add_comm (work t) extra, Function.iterate_add_apply, visit_steps, List.nil_append]
  exact Function.iterate_fixed rfl extra

def programBudget : List Instruction → ℕ
  | [] => 0
  | .visit t :: rest => t.toData.size + programBudget rest
  | .join _ :: rest => 1 + programBudget rest

theorem step_budget_le (s : State) : programBudget (step s).todo ≤ programBudget s.todo := by
  rcases s with ⟨todo, values, next, result⟩
  cases todo with
  | nil => exact le_rfl
  | cons ins rest =>
    cases ins with
    | visit t => cases t <;> simp only [step, programBudget, Term.dataSize_add, Term.dataSize_mul] <;> omega
    | join multiply => cases values with
      | nil => exact le_rfl
      | cons right tail => cases tail with
        | nil => exact le_rfl
        | cons left values => simp only [step, programBudget]; omega

theorem step_next_le (s : State) : (step s).next ≤ s.next + 1 := by
  rcases s with ⟨todo, values, next, result⟩
  cases todo with
  | nil => exact Nat.le_succ _
  | cons ins rest =>
    cases ins with
    | visit t => cases t <;> simp [step]
    | join multiply => cases values with
      | nil => exact Nat.le_succ _
      | cons right tail => cases tail <;> simp [step]

theorem step_valueCount_le (s : State) : (step s).values.length ≤ s.values.length + 1 := by
  rcases s with ⟨todo, values, next, result⟩
  cases todo with
  | nil => exact Nat.le_succ _
  | cons ins rest =>
    cases ins with
    | visit t => cases t <;> simp [step]
    | join multiply => cases values with
      | nil => exact Nat.le_succ _
      | cons right tail => cases tail <;> simp [step]

theorem step_values_le (s : State) (B : ℕ) (hn : s.next ≤ B)
    (hv : ∀ i ∈ s.values, i ≤ B) (hb : programBudget s.todo ≤ B) :
    ∀ i ∈ (step s).values, i ≤ B + 1 := by
  rcases s with ⟨todo, values, next, result⟩
  dsimp only at hn hv hb
  cases todo with
  | nil => exact fun i hi => (hv i hi).trans (Nat.le_succ _)
  | cons ins rest =>
    cases ins with
    | visit t =>
      cases t with
      | const z =>
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · exact (hv i hi).trans (Nat.le_succ _)
      | var v =>
        have ha : v + 1 ≤ (Term.var v).toData.size := Term.arity_le_dataSize (.var v)
        have hh : (Term.var v).toData.size ≤ B := by simp only [programBudget] at hb; omega
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · omega
        · exact (hv i hi).trans (Nat.le_succ _)
      | add a b => exact fun i hi => (hv i hi).trans (Nat.le_succ _)
      | mul a b => exact fun i hi => (hv i hi).trans (Nat.le_succ _)
    | join multiply =>
      cases values with
      | nil => simp [step]
      | cons right tail => cases tail with
        | nil => exact fun i hi => (hv i hi).trans (Nat.le_succ _)
        | cons left values =>
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · omega
          · exact (hv i (by simp [hi])).trans (Nat.le_succ _)

theorem run_bounds (t : Term) (start n : ℕ) :
    let s := step^[n] ⟨[.visit t], [], start, []⟩
    programBudget s.todo ≤ t.toData.size ∧ s.next ≤ start + n ∧ s.values.length ≤ n ∧
      ∀ i ∈ s.values, i ≤ start + t.toData.size + n := by
  induction n with
  | zero => simp [programBudget]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with ⟨hb, hn, hc, hv⟩
    refine ⟨(step_budget_le _).trans hb, (step_next_le _).trans ?_, (step_valueCount_le _).trans ?_, ?_⟩
    · omega
    · omega
    · have hn' : (step^[n] ⟨[.visit t], [], start, []⟩).next ≤ start + t.toData.size + n := by omega
      have hb' : programBudget (step^[n] ⟨[.visit t], [], start, []⟩).todo ≤ start + t.toData.size + n := by omega
      simpa only [Nat.add_assoc] using step_values_le _ _ hn' hv hb'

end LeanCanny.ETR.ComplexCircuit.Source.Machine
