/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Termination and clock bounds for the balanced product-bit controller

A global-index work allowance decreases at every nonterminal transition.
Together with live-query bounds this proves termination and the returned bit,
including the first halting time. Leaf access still counts as one abstract step.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct

def weight (K : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => limit K * (2 * weight K h + 3) + 2

theorem weight_pos (K h : ℕ) : 0 < weight K h := by
  cases h <;> simp only [weight] <;> omega

theorem weight_expand (K h : ℕ) (hh : 0 < h) :
    weight K h = limit K * (2 * weight K (h - 1) + 3) + 2 := by
  cases h with
  | zero => omega
  | succ h => rfl

def scanWork (K : ℕ) (q : Query) (t : ℕ) : ℕ :=
  (limit q.index - t) * (2 * weight K (q.height - 1) + 3) + 1

def Frame.work (K : ℕ) : Frame → ℕ
  | .left q t _ => weight K (q.height - 1) + 2 + scanWork K q (t + 1)
  | .right q t _ _ => 1 + scanWork K q (t + 1)

def stackWork (K : ℕ) : List Frame → ℕ
  | [] => 1
  | f :: stack => f.work K + stackWork K stack

def stateWork (K : ℕ) : State → ℕ
  | .eval q stack => weight K q.height + stackWork K stack
  | .scan q t _ stack => scanWork K q t + stackWork K stack
  | .ret _ stack => stackWork K stack
  | .done _ => 0

theorem step_work (a : ℕ → ℕ) (H K : ℕ) (s : State) (hs : Fits H K s) (hn : isDone s = false) :
    stateWork K (step a s) + 1 ≤ stateWork K s := by
  cases s with
  | eval q stack =>
    obtain ⟨hq, _⟩ := hs
    by_cases hh : q.height = 0
    · simp [step, hh, stateWork, weight, Nat.add_comm]
    · have hlim := limit_mono hq.2.1
      have he := Nat.mul_le_mul_right (2 * weight K (q.height - 1) + 3) hlim
      simp only [step, hh, ↓reduceIte, stateWork, scanWork, Nat.sub_zero,
        weight_expand K q.height (by omega)]
      omega
  | scan q t acc stack =>
    obtain ⟨_, _, ht, _⟩ := hs
    by_cases hend : limit q.index ≤ t
    · simp [step, hend, stateWork, scanWork, Nat.sub_eq_zero_of_le hend, Nat.add_comm]
    · have hsub : limit q.index - t = (limit q.index - (t + 1)) + 1 := by omega
      by_cases hi : position q.index t < count q.index
      · simp only [step, hend, hi, ↓reduceIte, stateWork, stackWork, Frame.work, Query.left, scanWork]
        rw [hsub, Nat.add_mul, one_mul]
        omega
      · simp only [step, hend, hi, ↓reduceIte, stateWork, scanWork]
        rw [hsub, Nat.add_mul, one_mul]
        omega
  | ret x stack =>
    cases stack with
    | nil => simp [step, stateWork, stackWork]
    | cons f stack =>
      cases f <;> simp only [step, stateWork, stackWork, Frame.work, Query.right] <;> omega
  | done x => simp [isDone] at hn

theorem exists_done_le (a : ℕ → ℕ) (H K : ℕ) (s : State) (hs : Fits H K s) :
    ∃ t ≤ stateWork K s, isDone ((step a)^[t] s) = true := by
  generalize heq : stateWork K s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hd : isDone s = true
    · exact ⟨0, Nat.zero_le _, hd⟩
    · have hn : isDone s = false := Bool.eq_false_iff.mpr hd
      have hw := step_work a H K s hs hn
      have hs' := step_fits a H K s hs
      obtain ⟨t, ht, hdone⟩ := ih (stateWork K (step a s)) (by omega) (step a s) hs' rfl
      refine ⟨t + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hdone

theorem has_halt (a : ℕ → ℕ) (H K : ℕ) : ∃ t, isDone ((step a)^[t] (start H K)) = true := by
  obtain ⟨t, _, ht⟩ := exists_done_le a H K (start H K) (start_fits H K)
  exact ⟨t, ht⟩

noncomputable def time (a : ℕ → ℕ) (H K : ℕ) : ℕ := Nat.find (has_halt a H K)

theorem before (a : ℕ → ℕ) (H K t : ℕ) (ht : t < time a H K) :
    isDone ((step a)^[t] (start H K)) = false :=
  Bool.eq_false_iff.mpr (Nat.find_min (has_halt a H K) ht)

theorem after (a : ℕ → ℕ) (H K : ℕ) : isDone ((step a)^[time a H K] (start H K)) = true :=
  Nat.find_spec (has_halt a H K)

theorem time_le (a : ℕ → ℕ) (H K : ℕ) : time a H K ≤ weight K H + 1 := by
  obtain ⟨t, ht, hd⟩ := exists_done_le a H K (start H K) (start_fits H K)
  have hf := Nat.find_min' (has_halt a H K) hd
  exact hf.trans (by simpa only [start, stateWork, stackWork] using ht)

theorem result (a : ℕ → ℕ) (H K : ℕ) :
    ∃ b, (step a)^[time a H K] (start H K) = .done b ∧ b = (tree a H 0).testBit K := by
  have hd := after a H K
  have hc := iterate_correct a ((tree a H 0).testBit K) (start H K) (start_correct a H K) (time a H K)
  cases he : (step a)^[time a H K] (start H K) <;> simp only [he, isDone, Bool.false_eq_true] at hd
  rename_i b
  exact ⟨b, rfl, by simpa only [he, Correct] using hc⟩

theorem weight_le (K H : ℕ) : weight K H ≤ (5 * limit K + 3) ^ H := by
  induction H with
  | zero => simp [weight]
  | succ H ih =>
    have hp := weight_pos K H
    have hm := Nat.mul_le_mul_left (5 * limit K + 3) ih
    rw [weight, pow_succ]
    nlinarith

theorem limit_base_bound (K : ℕ) : 5 * limit K + 3 ≤ 2 ^ (2 * K.size + 5) := by
  have hk : K + 1 ≤ 2 ^ K.size := by have := Nat.lt_size_self K; omega
  have he := Nat.mul_le_mul hk hk
  have hp : 0 < 2 ^ K.size := by positivity
  have hpow : 2 ^ (2 * K.size + 5) = (2 ^ K.size) * (2 ^ K.size) * 32 := by
    rw [pow_add, show 2 * K.size = K.size + K.size by omega, pow_add]
    rfl
  rw [hpow]
  unfold limit width count
  nlinarith

theorem time_exp_bound (a : ℕ → ℕ) (H K : ℕ) :
    time a H K ≤ 2 ^ (H * (2 * K.size + 5) + 1) := by
  have hw := weight_le K H
  have hb := Nat.pow_le_pow_left (limit_base_bound K) H
  have hp : 0 < 2 ^ (H * (2 * K.size + 5)) := by positivity
  have he : (2 ^ (2 * K.size + 5)) ^ H = 2 ^ (H * (2 * K.size + 5)) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [he] at hb
  have ht := (time_le a H K).trans (Nat.add_le_add_right (hw.trans hb) 1)
  rw [pow_succ]
  omega

end LeanCanny.Algebra.BalancedProduct
