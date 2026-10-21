/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderEncoding
import Mathlib.Tactic.Linarith

/-! # Complete task-stack size bounds for selected-monomial traversal -/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding

theorem iterate_pendingSize_le {R : Type*} [Monoid R] (constant : ℤ → R) (variableValue : ℕ → R)
    (s : State R) (k : ℕ) : pendingSize (((step constant variableValue)^[k] s).todo) ≤ pendingSize s.todo := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (pendingSize_step_le _ _ _).trans ih

theorem iterate_index_le {R : Type*} [Monoid R] (constant : ℤ → R) (variableValue : ℕ → R)
    (s : State R) (I k : ℕ) (hi : ∀ q ∈ s.todo, q.index ≤ I) :
    ∀ q ∈ ((step constant variableValue)^[k] s).todo, q.index ≤ I := by
  induction k with
  | zero => exact hi
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact index_le_step _ _ _ I ih

theorem taskStack_length_le (todo : List Task) (I : ℕ) (hi : ∀ q ∈ todo, q.index ≤ I) :
    (DynamicTreeFold.stackBits Task.encode todo).length ≤ (2 * I.size + 10) * pendingSize todo := by
  induction todo with
  | nil => simp [DynamicTreeFold.stackBits, pendingSize]
  | cons q rest ih =>
    have hq := Nat.size_le_size (hi q (List.mem_cons_self ..))
    have hr := ih (fun q h => hi q (List.mem_cons_of_mem _ h))
    have hp := @Data.size_pos q.term.toData
    have hs : 2 * I.size + 6 ≤ (2 * I.size + 6) * q.term.toData.size := Nat.le_mul_of_pos_right _ hp
    simp only [DynamicTreeFold.stackBits, Task.encode, pair_length, Data.length_toBits, BinaryNatCode.length_encode,
      pendingSize, List.map_cons, List.sum_cons] at *
    nlinarith

theorem context_encode_length_le {R : Type*} (code : R → List Bool) (s : State R) (c : List Bool) (I N : ℕ)
    (hi : ∀ q ∈ s.todo, q.index ≤ I) (hN : pendingSize s.todo ≤ N) :
    (pair c (s.encode code)).length ≤ 2 * c.length + 4 + (4 * I.size + 20) * N + (code s.value).length := by
  have ht := (taskStack_length_le s.todo I hi).trans (Nat.mul_le_mul_left _ hN)
  simp only [State.encode, pair_length]
  nlinarith

theorem initial_encode_length_le {R : Type*} [Monoid R] (constant : ℤ → R) (variableValue : ℕ → R)
    (code : R → List Bool) (t : Term) (r k : ℕ) (c : List Bool) :
    (pair c (((step constant variableValue)^[k] ⟨[⟨t, r⟩], 1⟩).encode code)).length ≤
      2 * c.length + 4 + (4 * r.size + 20) * t.toData.size +
        (code ((step constant variableValue)^[k] ⟨[⟨t, r⟩], 1⟩).value).length := by
  apply context_encode_length_le code _ c r t.toData.size
  · exact iterate_index_le _ _ _ r k (by simp)
  · simpa only [pendingSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using
      iterate_pendingSize_le constant variableValue (⟨[⟨t, r⟩], 1⟩ : State R) k

end LeanCanny.ETR.MonomialReader
