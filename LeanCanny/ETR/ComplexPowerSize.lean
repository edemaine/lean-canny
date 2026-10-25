/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexPowerCircuit
public import LeanCanny.ETR.ComplexCircuitBuilders

/-! # Explicit encoding budgets for binary-power networks -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit

theorem forest_nil : forest [] = [] := rfl

theorem forest_append (a b : List Gate) : forest (a ++ b) = forest a ++ forest b := by
  simp only [forest, List.map_append, List.flatten_append]

theorem mul_gate_length (out left right : ℕ) :
    (Gate.mul out left right).encode.length = 2 * out + 2 * left + 2 * right + 18 := by
  simp only [Gate.encode, Gate.toData, pairData, Data.length_toBits, Data.cons_size, Codec.unary_size, Data.size_empty]
  omega

theorem one_gate_length (out : ℕ) : (Gate.constant out 1).encode.length = 2 * out + 22 := by
  have hb : (1 : ℕ).bits = [true] := by decide
  have hc : (Term.const 1).toData.size = 14 := by
    simp [Term.toData, Codec.integer, Codec.natural, hb, Codec.bit, Data.cons_size, Codec.unary_size, Data.size_empty]
  simp only [Gate.encode, Gate.toData, pairData, Data.length_toBits, Data.cons_size, Codec.unary_size, Data.size_empty, hc]
  omega

namespace Power

def stepBudget (base start k : ℕ) : ℕ := 10 * (start + 2 * k) + 2 * (base + start) + 44
def forestBudget (base start k : ℕ) : ℕ := 2 * start + 22 + k * stepBudget base start k
def stateBudget (base start k : ℕ) : ℕ := 2 * (start + 2 * k) + 2 + forestBudget base start k

theorem stepBudget_mono (base start : ℕ) {a b : ℕ} (hab : a ≤ b) :
    stepBudget base start a ≤ stepBudget base start b := by unfold stepBudget; omega

theorem forestBudget_mono (base start : ℕ) {a b : ℕ} (hab : a ≤ b) :
    forestBudget base start a ≤ forestBudget base start b :=
  Nat.add_le_add_left (Nat.mul_le_mul hab (stepBudget_mono base start hab)) _

theorem forest_length_le (base start : ℕ) (bits : List Bool) :
    (forest (gates base start bits)).length ≤ forestBudget base start bits.length := by
  induction bits with
  | nil =>
    simp only [gates_nil, forest_cons, forest_nil, List.length_append,
      List.length_nil, Nat.add_zero, one_gate_length, forestBudget, Nat.zero_mul]
    exact le_rfl
  | cons b bits ih =>
    rw [gates_cons, forest_append, List.length_append]
    have hn : (forest [Gate.mul (output start bits + 1) (output start bits) (output start bits),
        Gate.mul (output start bits + 2) (output start bits + 1) (if b then base else start)]).length ≤
        stepBudget base start bits.length := by
      simp only [forest_cons, forest_nil, List.length_append, List.length_nil,
        Nat.add_zero, mul_gate_length, output, stepBudget]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
    apply (Nat.add_le_add ih hn).trans
    simp only [forestBudget, List.length_cons]
    calc
      2 * start + 22 + bits.length * stepBudget base start bits.length +
          stepBudget base start bits.length =
          2 * start + 22 + (bits.length + 1) * stepBudget base start bits.length := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      _ ≤ 2 * start + 22 + (bits.length + 1) * stepBudget base start (bits.length + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (bits.length + 1)
          (stepBudget_mono base start (Nat.le_add_right bits.length 1))) _

end Power
end LeanCanny.ETR.ComplexCircuit
