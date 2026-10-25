/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuit

/-! # Completion of acyclic complex arithmetic networks

An operation list assigns consecutive fresh wires and reads only earlier
wires. Every input assignment has a completion satisfying all generated gate
constraints, and the completion preserves every earlier input coordinate.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open scoped Classical

def Gate.arity : Gate → ℕ
  | .constant out _ => out + 1
  | .add out left right | .mul out left right => max (out + 1) (max (left + 1) (right + 1))
  | .zero wire => wire + 1

theorem Gate.holds_congr (g : Gate) (env env' : ℕ → ℂ)
    (h : ∀ i < g.arity, env i = env' i) : g.Holds env ↔ g.Holds env' := by
  cases g with
  | constant out z => simp only [Gate.Holds, h out (by simp [Gate.arity])]
  | add out left right =>
    have ho := h out (by simp [Gate.arity])
    have hl := h left (by simp [Gate.arity])
    have hr := h right (by simp [Gate.arity])
    simp only [Gate.Holds, ho, hl, hr]
  | mul out left right =>
    have ho := h out (by simp [Gate.arity])
    have hl := h left (by simp [Gate.arity])
    have hr := h right (by simp [Gate.arity])
    simp only [Gate.Holds, ho, hl, hr]
  | zero wire => simp only [Gate.Holds, h wire (by simp [Gate.arity])]

inductive Operation where
  | constant (value : ℤ)
  | add (left right : ℕ)
  | mul (left right : ℕ)
  deriving DecidableEq, Repr

noncomputable def Operation.eval (env : ℕ → ℂ) : Operation → ℂ
  | .constant z => z
  | .add left right => env left + env right
  | .mul left right => env left * env right

def Operation.InputsBelow (out : ℕ) : Operation → Prop
  | .constant _ => True
  | .add left right | .mul left right => left < out ∧ right < out

def Operation.gate (out : ℕ) : Operation → Gate
  | .constant z => .constant out z
  | .add left right => .add out left right
  | .mul left right => .mul out left right

theorem Operation.gate_holds_iff (op : Operation) (out : ℕ) (env : ℕ → ℂ) :
    (op.gate out).Holds env ↔ env out = op.eval env := by cases op <;> rfl

theorem Operation.eval_congr (op : Operation) (out : ℕ) (env env' : ℕ → ℂ)
    (hop : op.InputsBelow out) (h : ∀ i < out, env i = env' i) : op.eval env = op.eval env' := by
  cases op with
  | constant z => rfl
  | add left right => simp only [Operation.eval, h left hop.1, h right hop.2]
  | mul left right => simp only [Operation.eval, h left hop.1, h right hop.2]

theorem Operation.gate_arity (op : Operation) (out : ℕ) (hop : op.InputsBelow out) :
    (op.gate out).arity ≤ out + 1 := by
  cases op <;> simp only [Operation.gate, Gate.arity, Operation.InputsBelow] at * <;> omega

namespace StraightLine

def WellFormed : ℕ → List Operation → Prop
  | _, [] => True
  | start, op :: ops => op.InputsBelow start ∧ WellFormed (start + 1) ops

def gates : ℕ → List Operation → List Gate
  | _, [] => []
  | start, op :: ops => op.gate start :: gates (start + 1) ops

noncomputable def run (env : ℕ → ℂ) : ℕ → List Operation → ℕ → ℂ
  | _, [] => env
  | start, op :: ops => run (Function.update env start (op.eval env)) (start + 1) ops

theorem run_preserves_before (env : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (i : ℕ) (hi : i < start) : run env start ops i = env i := by
  induction ops generalizing env start with
  | nil => rfl
  | cons op ops ih =>
    rw [run, ih _ _ (by omega)]
    exact Function.update_of_ne (show i ≠ start by omega) _ _

theorem run_satisfies (env : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) : ∀ g ∈ gates start ops, g.Holds (run env start ops) := by
  induction ops generalizing env start with
  | nil => simp [gates]
  | cons op ops ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · apply (Operation.gate_holds_iff op start _).mpr
      have ho : run env start (op :: ops) start = op.eval env := by
        rw [run, run_preserves_before _ (start + 1) ops start (by omega), Function.update_self]
      have hp : ∀ i < start, run env start (op :: ops) i = env i :=
        fun i hi => run_preserves_before env start (op :: ops) i hi
      exact ho.trans (Operation.eval_congr op start _ env hw.1 hp).symm
    · exact ih _ _ hw.2 g hg

theorem exists_completion (env : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) :
    ∃ out : ℕ → ℂ, (∀ i < start, out i = env i) ∧ ∀ g ∈ gates start ops, g.Holds out :=
  ⟨run env start ops, fun i hi => run_preserves_before env start ops i hi, run_satisfies env start ops hw⟩

theorem gates_length (start : ℕ) (ops : List Operation) : (gates start ops).length = ops.length := by
  induction ops generalizing start <;> simp_all [gates]

theorem gates_arity (start : ℕ) (ops : List Operation) (hw : WellFormed start ops)
    (g : Gate) (hg : g ∈ gates start ops) : g.arity ≤ start + ops.length := by
  induction ops generalizing start with
  | nil => simp [gates] at hg
  | cons op ops ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · have ho := Operation.gate_arity op start hw.1
      simp only [List.length_cons]
      omega
    · have ht := ih (start + 1) hw.2 hg
      simp only [List.length_cons]
      omega

theorem wellFormed_append (start : ℕ) (a b : List Operation) :
    WellFormed start (a ++ b) ↔ WellFormed start a ∧ WellFormed (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [WellFormed]
  | cons op ops ih =>
    simp only [List.cons_append, WellFormed, List.length_cons, ih]
    have he : start + 1 + ops.length = start + (ops.length + 1) := by omega
    rw [he]
    tauto

theorem gates_append (start : ℕ) (a b : List Operation) :
    gates start (a ++ b) = gates start a ++ gates (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [gates]
  | cons op ops ih =>
    simp only [List.cons_append, gates, List.length_cons, ih]
    rw [show start + 1 + ops.length = start + (ops.length + 1) by omega]

end StraightLine
end LeanCanny.ETR.ComplexCircuit
