/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerMachine

/-!
# Termination and correctness of the streamed power machine

A natural-valued potential decreases by exactly one at every nonterminal
transition. Thus the work recurrence bounds the actual abstract-machine run,
including both calls for every summand and the switches between them.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower

variable {R : Type*} [Semiring R] {n : ℕ}

def branchWork (q : Query n) : ℕ :=
  work n (q.height - 1) (q.exponent / 2) +
    work n (q.height - 1) (q.exponent - q.exponent / 2) + 2

def Frame.work : Frame R n → ℕ
  | .left q k _ =>
      MatrixPower.work n (q.height - 1) (q.exponent - q.exponent / 2) + 2 +
        k.val * branchWork q
  | .right q k _ _ => 1 + k.val * branchWork q

def stackWork : List (Frame R n) → ℕ
  | [] => 1
  | f :: stack => f.work + stackWork stack

def stateWork : State R n → ℕ
  | .eval q stack => q.work + stackWork stack
  | .ret _ stack => stackWork stack
  | .done _ => 0

theorem query_work_expand (q : Query n) (hh : 0 < q.height) (he : 1 < q.exponent) :
    q.work = 1 + n * branchWork q := by
  rcases q with ⟨h, e, i, j⟩
  change 0 < h at hh
  change 1 < e at he
  cases h with
  | zero => omega
  | succ h =>
      simp only [Query.work, work, show ¬ e ≤ 1 by omega, ↓reduceIte, branchWork,
        Nat.add_sub_cancel]

theorem step_work (A : Matrix (Fin n) (Fin n) R) (s : State R n)
    (hs : ∀ x, s ≠ .done x) : stateWork (step A s) + 1 = stateWork s := by
  cases s with
  | eval q stack =>
      by_cases he0 : q.exponent = 0
      · have hq : q.work = 1 := by
          cases h : q.height <;> simp [Query.work, work, h, he0]
        simp [step, he0, stateWork, hq, Nat.add_comm]
      by_cases he1 : q.exponent = 1
      · have hq : q.work = 1 := by
          cases h : q.height <;> simp [Query.work, work, h, he1]
        simp [step, he1, stateWork, hq, Nat.add_comm]
      by_cases hh : q.height = 0
      · simp [step, he0, he1, hh, stateWork, Query.work, work, Nat.add_comm]
      · change stateWork (step A (.eval q stack)) + 1 = q.work + stackWork stack
        rw [query_work_expand q (by omega) (by omega)]
        simp only [step, he0, he1, hh, ↓reduceIte, stateWork, stackWork, Frame.work,
          Query.work, Query.left, Query.last]
        have hn : n - 1 + 1 = n := by have := q.row.isLt; omega
        unfold branchWork
        nlinarith
  | ret x stack =>
      cases stack with
      | nil => rfl
      | cons f stack =>
          cases f with
          | left q k acc =>
              simp only [step, stateWork, stackWork, Frame.work, Query.work, Query.right]
              omega
          | right q k acc lhs =>
              by_cases hk : k.val = 0
              · simp [step, hk, stateWork, stackWork, Frame.work, Nat.add_comm]
              · simp only [step, hk, ↓reduceIte, stateWork, stackWork, Frame.work,
                  Query.work, Query.left]
                have hk' : k.val - 1 + 1 = k.val := by omega
                unfold branchWork
                nlinarith
  | done x => exact (hs x rfl).elim

omit [Semiring R] in
theorem stateWork_zero (s : State R n) (hs : stateWork s = 0) : ∃ x, s = .done x := by
  have hstack : ∀ stack : List (Frame R n), 0 < stackWork stack := by
    intro stack
    induction stack with
    | nil => simp only [stackWork]; omega
    | cons f stack ih => simp only [stackWork]; omega
  cases s with
  | eval q stack => have := hstack stack; simp only [stateWork] at hs; omega
  | ret x stack => have := hstack stack; simp only [stateWork] at hs; omega
  | done x => exact ⟨x, rfl⟩

theorem iterate_value (A : Matrix (Fin n) (Fin n) R) (t : ℕ) (s : State R n) :
    value A ((step A)^[t] s) = value A s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', step_value, ih]

theorem iterate_done (A : Matrix (Fin n) (Fin n) R) (s : State R n) :
    ∃ x, (step A)^[stateWork s] s = .done x := by
  generalize heq : stateWork s = t
  induction t using Nat.strong_induction_on generalizing s with
  | h t ih =>
      by_cases ht : t = 0
      · obtain ⟨x, hx⟩ := stateWork_zero s (heq.trans ht)
        exact ⟨x, by simpa only [ht, Function.iterate_zero, id_eq] using hx⟩
      · have hs : ∀ x, s ≠ .done x := by
          intro x hx
          subst s
          simp only [stateWork] at heq
          omega
        have hw := step_work A s hs
        obtain ⟨x, hx⟩ := ih (stateWork (step A s)) (by omega) (step A s) rfl
        refine ⟨x, ?_⟩
        have ht' : t = stateWork (step A s) + 1 := by omega
        rw [ht', Function.iterate_succ_apply]
        exact hx

/-- Exact abstract-machine evaluation of a query, including the final transition
from an empty return stack to a terminal state. -/
theorem run_query (A : Matrix (Fin n) (Fin n) R) (q : Query n) :
    (step A)^[q.work + 1] (.eval q []) = .done (q.value A) := by
  obtain ⟨x, hx⟩ := iterate_done A (.eval q [])
  change (step A)^[q.work + 1] (.eval q []) = .done x at hx
  have hv := iterate_value A (q.work + 1) (.eval q [])
  rw [hx] at hv
  change x = q.value A at hv
  simpa only [hv] using hx

theorem run_pow (A : Matrix (Fin n) (Fin n) R) (e : ℕ) (i j : Fin n) :
    (step A)^[work n e.size e + 1] (.eval ⟨e.size, e, i, j⟩ []) = .done ((A ^ e) i j) := by
  simpa only [Query.work, Query.value, entry_size_eq_pow] using
    run_query A ⟨e.size, e, i, j⟩

end LeanCanny.Algebra.MatrixPower
