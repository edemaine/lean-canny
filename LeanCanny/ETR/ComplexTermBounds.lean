/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermStepEncoding
public import LeanCanny.ETR.ComplexPowerSize

/-! # Literal bounds throughout source-circuit compilation -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source.Machine
open LeanCanny.Encoding

theorem constant_gate_length (out : ℕ) (z : ℤ) :
    (Gate.constant out z).encode.length = 2 * out + 8 + (Term.const z).toData.size := by
  simp only [Gate.encode, Gate.toData, pairData, Data.length_toBits, Data.cons_size,
    Codec.unary_size, Data.size_empty]
  omega

theorem add_gate_length (out left right : ℕ) :
    (Gate.add out left right).encode.length = 2 * out + 2 * left + 2 * right + 16 := by
  simp only [Gate.encode, Gate.toData, pairData, Data.length_toBits, Data.cons_size,
    Codec.unary_size, Data.size_empty]
  omega

theorem step_result_length_le (s : State) (B S : ℕ) (hn : s.next ≤ B)
    (hv : ∀ i ∈ s.values, i ≤ B) (hb : programBudget s.todo ≤ S) :
    (forest (step s).result).length ≤ (forest s.result).length + (6 * B + S + 22) := by
  rcases s with ⟨todo, values, next, result⟩
  dsimp only at hn hv hb
  cases todo with
  | nil => simp [step]
  | cons ins rest =>
    cases ins with
    | visit t =>
      cases t with
      | const z =>
        simp only [programBudget] at hb
        simp only [step, forest_append, forest_cons, forest_nil, List.length_append,
          List.append_nil, constant_gate_length]
        omega
      | var i => simp [step]
      | add a b => simp [step]
      | mul a b => simp [step]
    | join multiply =>
      cases values with
      | nil => simp [step]
      | cons right tail => cases tail with
        | nil => simp [step]
        | cons left values =>
          have hr := hv right (by simp)
          have hl := hv left (by simp)
          cases multiply <;> simp only [step, Bool.false_eq_true, ite_false, ite_true,
            forest_append, forest_cons, forest_nil, List.length_append, List.append_nil,
            add_gate_length, mul_gate_length] <;> omega

theorem programStack_length_le (todo : List Instruction) :
    (DynamicTreeFold.stackBits Instruction.encode todo).length ≤ 6 * programBudget todo := by
  induction todo with
  | nil => simp [DynamicTreeFold.stackBits, programBudget]
  | cons ins rest ih =>
    cases ins with
    | visit t =>
      have hp := @Data.size_pos t.toData
      simp only [DynamicTreeFold.stackBits, pair_length, Instruction.encode, List.length_cons,
        Data.length_toBits, programBudget]
      omega
    | join multiply =>
      simp only [DynamicTreeFold.stackBits, pair_length, Instruction.encode, List.length_cons,
        List.length_nil, programBudget]
      omega

theorem valueStack_length_le (values : List ℕ) (B : ℕ) (hv : ∀ i ∈ values, i ≤ B) :
    (DynamicTreeFold.stackBits (fun i => List.replicate i true) values).length ≤ (2 * B + 2) * values.length := by
  induction values with
  | nil => simp [DynamicTreeFold.stackBits]
  | cons i values ih =>
    have hi := hv i (by simp)
    have hh := ih (fun j hj => hv j (by simp [hj]))
    simp only [DynamicTreeFold.stackBits, pair_length, List.length_replicate,
      List.length_cons, Nat.mul_succ]
    omega

theorem State.encode_length_le (s : State) (B : ℕ) (hv : ∀ i ∈ s.values, i ≤ B) :
    s.encode.length ≤ 12 * programBudget s.todo + (4 * B + 4) * s.values.length +
      2 * s.next + 6 + (forest s.result).length := by
  have ht := programStack_length_le s.todo
  have hh := valueStack_length_le s.values B hv
  simp only [State.encode, pair_length, List.length_replicate]
  calc
    _ ≤ 2 * (6 * programBudget s.todo) + 2 +
        (2 * ((2 * B + 2) * s.values.length) + 2 + (2 * s.next + 2 + (forest s.result).length)) := by omega
    _ = _ := by ring

theorem run_result_length_le (t : Term) (start N n : ℕ) (hn : n ≤ N) :
    (forest (step^[n] ⟨[.visit t], [], start, []⟩).result).length ≤
      n * (6 * (start + t.toData.size + N) + t.toData.size + 22) := by
  induction n with
  | zero => simp [forest]
  | succ n ih =>
    have hi := ih (by omega)
    have hb := run_bounds t start n
    have hh := step_result_length_le (step^[n] ⟨[.visit t], [], start, []⟩)
      (start + t.toData.size + N) t.toData.size (by have := hb.2.1; omega)
      (fun i h => by have := hb.2.2.2 i h; omega) hb.1
    rw [Function.iterate_succ_apply']
    rw [Nat.succ_mul]
    omega

theorem run_encode_length_le (t : Term) (start N n : ℕ) (hn : n ≤ N) :
    (step^[n] ⟨[.visit t], [], start, []⟩).encode.length ≤
      100 * (start + t.toData.size + N + 1) ^ 2 := by
  have hb := run_bounds t start n
  let B := start + t.toData.size + N
  have hv : ∀ i ∈ (step^[n] ⟨[.visit t], [], start, []⟩).values, i ≤ B := by
    intro i hi
    have := hb.2.2.2 i hi
    dsimp only [B]
    omega
  have he := State.encode_length_le (step^[n] ⟨[.visit t], [], start, []⟩) B hv
  have hr := (run_result_length_le t start N n hn).trans
    (Nat.mul_le_mul_right _ hn)
  have hm := Nat.mul_le_mul_left (4 * B + 4) (hb.2.2.1.trans hn)
  calc
    _ ≤ 12 * t.toData.size + (4 * B + 4) * N + 2 * (start + N) + 6 +
        N * (6 * B + t.toData.size + 22) := by
      dsimp only [B] at he hm ⊢
      omega
    _ ≤ _ := by
      dsimp only [B]
      nlinarith [Nat.zero_le (start * t.toData.size), Nat.zero_le (start * N), Nat.zero_le (t.toData.size * N)]

end LeanCanny.ETR.ComplexCircuit.Source.Machine
