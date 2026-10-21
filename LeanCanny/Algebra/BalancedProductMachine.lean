/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProduct
public import Mathlib.Logic.Function.Iterate

/-!
# A uniform continuation machine for balanced product bits

Each positive-height query scans the columns of its two-child product.
The active frame retains a binary scan counter, a small column accumulator,
and at most one returned bit. Leaf bit access is abstract at this stage;
encoded FP control and space-bounded leaf costs are supplied separately.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct

inductive Frame where
  | left (parent : Query) (time accumulator : ℕ)
  | right (parent : Query) (time accumulator : ℕ) (selector : Bool)
deriving DecidableEq

inductive State where
  | eval (query : Query) (stack : List Frame)
  | scan (query : Query) (time accumulator : ℕ) (stack : List Frame)
  | ret (value : Bool) (stack : List Frame)
  | done (value : Bool)
deriving DecidableEq

def contribution (q : Query) (t : ℕ) (left right : Bool) : ℕ :=
  if left && decide (position q.index t ≤ column q.index t) && right then 1 else 0

def step (a : ℕ → ℕ) : State → State
  | .eval q stack =>
      if q.height = 0 then .ret ((a q.node).testBit q.index) stack else .scan q 0 0 stack
  | .scan q t acc stack =>
      if limit q.index ≤ t then .ret (decide (acc % 2 = 1)) stack
      else if position q.index t < count q.index then .eval (q.left t) (.left q t acc :: stack)
      else .scan q (t + 1) (acc / 2) stack
  | .ret x [] => .done x
  | .ret x (.left q t acc :: stack) => .eval (q.right t) (.right q t acc x :: stack)
  | .ret y (.right q t acc lhs :: stack) => .scan q (t + 1) (acc + contribution q t lhs y) stack
  | .done x => .done x

def isDone : State → Bool
  | .done _ => true
  | _ => false

def Active (q : Query) (t : ℕ) : Prop :=
  0 < q.height ∧ t < limit q.index ∧ position q.index t < count q.index

def StackCorrect (a : ℕ → ℕ) (out : Bool) : List Frame → Bool → Prop
  | [], x => x = out
  | .left q t acc :: stack, x =>
      x = (q.left t).value a ∧ Active q t ∧ acc = q.carry a t ∧ StackCorrect a out stack (q.value a)
  | .right q t acc lhs :: stack, x =>
      x = (q.right t).value a ∧ lhs = (q.left t).value a ∧ Active q t ∧
        acc = q.carry a t ∧ StackCorrect a out stack (q.value a)

def Correct (a : ℕ → ℕ) (out : Bool) : State → Prop
  | .eval q stack => StackCorrect a out stack (q.value a)
  | .scan q t acc stack =>
      0 < q.height ∧ t ≤ limit q.index ∧ acc = q.carry a t ∧ StackCorrect a out stack (q.value a)
  | .ret x stack => StackCorrect a out stack x
  | .done x => x = out

theorem contribution_eq (a : ℕ → ℕ) (q : Query) (t : ℕ) :
    contribution q t ((q.left t).value a) ((q.right t).value a) =
      BinarySum.bit (q.terms a (position q.index t)) (column q.index t) := by
  rw [BinarySum.bit_eq, q.term_bit]
  rfl

theorem step_correct (a : ℕ → ℕ) (out : Bool) (s : State) (hs : Correct a out s) :
    Correct a out (step a s) := by
  cases s with
  | eval q stack =>
    by_cases hh : q.height = 0
    · simpa only [step, hh, ↓reduceIte, Correct, Query.value, tree] using hs
    · simp only [step, hh, ↓reduceIte, Correct]
      exact ⟨by omega, Nat.zero_le _, (BinarySum.carryValue_zero _ _).symm, hs⟩
  | scan q t acc stack =>
    obtain ⟨hh, ht, ha, hs⟩ := hs
    by_cases hend : limit q.index ≤ t
    · have he : t = limit q.index := by omega
      simpa only [step, ha, he, Nat.le_refl, ↓reduceIte, Correct, q.result a hh] using hs
    · by_cases hi : position q.index t < count q.index
      · simp only [step, hend, hi, ↓reduceIte, Correct, StackCorrect]
        exact ⟨True.intro, ⟨hh, by omega, hi⟩, ha, hs⟩
      · simp only [step, hend, hi, ↓reduceIte, Correct]
        refine ⟨hh, by omega, ?_, hs⟩
        rw [ha]
        exact (BinarySum.carryValue_succ_carry (count q.index) (q.terms a) t hi).symm
  | ret x stack =>
    cases stack with
    | nil => exact hs
    | cons f stack =>
      cases f with
      | left q t acc =>
        obtain ⟨hx, hactive, ha, hs⟩ := hs
        exact ⟨rfl, hx, hactive, ha, hs⟩
      | right q t acc lhs =>
        obtain ⟨hx, hl, hactive, ha, hs⟩ := hs
        refine ⟨hactive.1, by have := hactive.2.1; omega, ?_, hs⟩
        rw [ha, hl, hx, contribution_eq]
        exact (BinarySum.carryValue_succ_bit (count q.index) (q.terms a) t hactive.2.2).symm
  | done x => exact hs

theorem iterate_correct (a : ℕ → ℕ) (out : Bool) (s : State) (hs : Correct a out s) (t : ℕ) :
    Correct a out ((step a)^[t] s) := by
  induction t with
  | zero => exact hs
  | succ t ih => rw [Function.iterate_succ_apply']; exact step_correct a out _ ih

end LeanCanny.Algebra.BalancedProduct
