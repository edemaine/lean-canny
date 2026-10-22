/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationSystemEncoding
public import LeanCanny.ETR.NegationNormalForm

/-!
# A sequential stack implementation of the equation compiler

Visits schedule the left child before the right child, followed by a join.
One counter carries the next fresh variable through the complete traversal.
The bounded run agrees exactly with `SignedFormula.equations`; no fresh-variable
renaming or alternative normalization semantics is introduced.
-/

@[expose] public section

namespace LeanCanny.ETR.EquationCompiler

inductive Instruction where
  | visit (p : SignedFormula)
  | join (disjoin : Bool)
  deriving DecidableEq, Repr

structure State where
  todo : List Instruction
  values : List EquationSystem
  next : ℕ
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.todo with
  | [] => s
  | .visit (.and p q) :: rest =>
      ⟨.visit p :: .visit q :: .join false :: rest, s.values, s.next⟩
  | .visit (.or p q) :: rest =>
      ⟨.visit p :: .visit q :: .join true :: rest, s.values, s.next⟩
  | .visit p :: rest =>
      let out := p.equations s.next
      ⟨rest, out :: s.values, out.next⟩
  | .join disjoin :: rest =>
      match s.values with
      | b :: a :: values =>
          let out := if disjoin then a.disjunction b else a.conjunction b
          ⟨rest, out :: values, out.next⟩
      | _ => s

def work : SignedFormula → ℕ
  | .and p q | .or p q => work p + work q + 2
  | _ => 1

theorem work_pos (p : SignedFormula) : 0 < work p := by
  cases p <;> simp [work]

theorem work_le_budget (p : SignedFormula) : work p ≤ 2 * p.budget := by
  induction p <;> simp only [work, SignedFormula.budget] at * <;> omega

@[simp] theorem step_done (values : List EquationSystem) (next : ℕ) :
    step ⟨[], values, next⟩ = ⟨[], values, next⟩ := rfl

/-- Exact compiler execution with an arbitrary surrounding continuation and value stack. -/
theorem visit_steps (p : SignedFormula) (todo : List Instruction)
    (values : List EquationSystem) (start : ℕ) :
    step^[work p] ⟨.visit p :: todo, values, start⟩ =
      ⟨todo, p.equations start :: values, (p.equations start).next⟩ := by
  induction p generalizing todo values start with
  | truth | falsum | eqZero t | neZero t | ltZero t | nonneg t => rfl
  | and p q ihp ihq =>
      rw [work, show work p + work q + 2 = (1 + work q + work p) + 1 by omega,
        Function.iterate_succ_apply]
      change step^[1 + work q + work p]
        ⟨.visit p :: .visit q :: .join false :: todo, values, start⟩ = _
      rw [Function.iterate_add_apply step (1 + work q) (work p), ihp,
        Function.iterate_add_apply step 1 (work q), ihq]
      rfl
  | or p q ihp ihq =>
      rw [work, show work p + work q + 2 = (1 + work q + work p) + 1 by omega,
        Function.iterate_succ_apply]
      change step^[1 + work q + work p]
        ⟨.visit p :: .visit q :: .join true :: todo, values, start⟩ = _
      rw [Function.iterate_add_apply step (1 + work q) (work p), ihp,
        Function.iterate_add_apply step 1 (work q), ihq]
      rfl

/-- Extra fuel is harmless once the complete program has terminated. -/
theorem run_steps (p : SignedFormula) (start fuel : ℕ) (hfuel : work p ≤ fuel) :
    step^[fuel] ⟨[.visit p], [], start⟩ =
      ⟨[], [p.equations start], (p.equations start).next⟩ := by
  obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hfuel
  rw [he, Nat.add_comm (work p) extra, Function.iterate_add_apply, visit_steps]
  exact Function.iterate_fixed (step_done _ _) extra

def compile (p : SignedFormula) (start : ℕ) : EquationSystem :=
  let final := step^[work p] ⟨[.visit p], [], start⟩
  final.values.headD ⟨[], final.next⟩

theorem compile_eq_equations (p : SignedFormula) (start : ℕ) :
    compile p start = p.equations start := by
  rw [compile, visit_steps]
  rfl

/-- At most twice the input bit length is enough fuel for a normalized formula. -/
theorem formula_run_steps (p : Formula) (start : ℕ) :
    step^[2 * p.encode.length] ⟨[.visit (p.toSigned true)], [], start⟩ =
      ⟨[], [(p.toSigned true).equations start], ((p.toSigned true).equations start).next⟩ := by
  apply run_steps
  have hw := work_le_budget (p.toSigned true)
  have hb := p.toSigned_budget_le true
  simp only [Formula.encode, LeanCanny.Data.length_toBits]
  omega

end LeanCanny.ETR.EquationCompiler
