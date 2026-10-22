/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Permanences
import Lean.Elab.Tactic.Omega

/-! # A streaming accumulator for permanences minus variations

The state retains the previous nonzero sign, the pending zero gap, and two
unsigned counts. Every counter is at most the number of entries processed.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignStatistic
open PrincipalSubresultant

structure State where
  previous : SignType
  gap : ℕ
  positive : ℕ
  negative : ℕ
  deriving DecidableEq

def initial : State := ⟨0, 0, 0, 0⟩
def State.value (s : State) : ℤ := (s.positive : ℤ) - s.negative
def contribution (s : State) (a : SignType) : ℤ :=
  zeroGapWeight s.gap * (s.previous : ℤ) * (a : ℤ)

theorem contribution_values (s : State) (a : SignType) :
    contribution s a = 0 ∨ contribution s a = 1 ∨ contribution s a = -1 := by
  have hw : zeroGapWeight s.gap = 0 ∨ zeroGapWeight s.gap = 1 ∨
      zeroGapWeight s.gap = -1 := by
    rw [zeroGapWeight_def]
    split_ifs
    · exact Or.inr (neg_one_pow_eq_or ℤ _)
    · exact Or.inl rfl
  rcases s with ⟨b, k, p, n⟩
  rcases hw with hw | hw | hw <;> cases b <;> cases a <;>
    simp_all [contribution]

def step (s : State) (a : SignType) : State :=
  if a = 0 then { s with gap := s.gap + 1 }
  else ⟨a, 0, s.positive + (if contribution s a = 1 then 1 else 0),
    s.negative + (if contribution s a = -1 then 1 else 0)⟩

theorem step_value (s : State) (a : SignType) :
    (step s a).value = s.value + contribution s a := by
  by_cases ha : a = 0
  · subst a
    simp [step, contribution, State.value]
  rcases contribution_values s a with h | h | h
  · simp [step, ha, h, State.value]
  all_goals
    simp [step, ha, h, State.value]
    omega

def run (s : State) (l : List SignType) : State := l.foldl step s

theorem run_value (s : State) (l : List SignType) :
    (run s l).value = s.value + signTail s.previous s.gap l := by
  induction l generalizing s with
  | nil => simp [run]
  | cons a l ih =>
    change (run (step s a) l).value = _
    rw [ih, step_value, signTail_cons]
    by_cases ha : a = 0
    · subst a
      simp [step, contribution]
    · simp only [ha, ↓reduceIte, step]
      unfold contribution
      omega

theorem run_initial_value (l : List SignType) :
    (run initial l).value = permanencesMinusVariations l := by
  rw [run_value, permanencesMinusVariations_eq_signTail]
  simp [initial, State.value]

def scan (a : ℕ → SignType) : ℕ → State
  | 0 => initial
  | k + 1 => step (scan a k) (a k)

theorem scan_eq_run (a : ℕ → SignType) (k : ℕ) :
    scan a k = run initial ((List.range k).map a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scan, ih, run, List.range_succ, List.foldl_append]

theorem scan_value (a : ℕ → SignType) (k : ℕ) :
    (scan a k).value = permanencesMinusVariations ((List.range k).map a) := by
  rw [scan_eq_run, run_initial_value]

theorem scan_bounds (a : ℕ → SignType) (k : ℕ) :
    (scan a k).gap ≤ k ∧ (scan a k).positive ≤ k ∧ (scan a k).negative ≤ k := by
  induction k with
  | zero => exact ⟨by rfl, by rfl, by rfl⟩
  | succ k ih =>
    simp only [scan, step]
    split_ifs <;> simp only <;> omega

end LeanCanny.Algebra.SignStatistic
