/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexStraightLine
public import LeanCanny.Encoding.NatBits

/-! # Shared complex power networks for binary exponents

The network allocates one constant-one wire and two multiplication wires per
exponent bit. Every satisfying assignment computes the exact power, and every
input assignment has a satisfying completion preserving its earlier wires.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Power
open scoped Classical

def output (start : ℕ) (bits : List Bool) : ℕ := start + 2 * bits.length

def program (base start : ℕ) : List Bool → List Operation
  | [] => [.constant 1]
  | b :: bits => program base start bits ++
      [.mul (output start bits) (output start bits),
        .mul (output start bits + 1) (if b then base else start)]

theorem program_length (base start : ℕ) (bits : List Bool) :
    (program base start bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [program, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem next_eq (base start : ℕ) (bits : List Bool) :
    start + (program base start bits).length = output start bits + 1 := by
  rw [program_length]
  unfold output
  omega

theorem output_cons (start : ℕ) (b : Bool) (bits : List Bool) :
    output start (b :: bits) = output start bits + 2 := by simp only [output, List.length_cons]; omega

theorem wellFormed (base start : ℕ) (hbase : base < start) (bits : List Bool) :
    StraightLine.WellFormed start (program base start bits) := by
  induction bits with
  | nil => simp [program, StraightLine.WellFormed, Operation.InputsBelow]
  | cons b bits ih =>
    rw [program, StraightLine.wellFormed_append, next_eq]
    refine ⟨ih, ?_⟩
    cases b <;> simp only [StraightLine.WellFormed, Operation.InputsBelow, Bool.false_eq_true,
      ite_false, ite_true, output]
    all_goals exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

def gates (base start : ℕ) (bits : List Bool) : List Gate := StraightLine.gates start (program base start bits)

theorem gates_nil (base start : ℕ) : gates base start [] = [.constant start 1] := rfl

theorem gates_cons (base start : ℕ) (b : Bool) (bits : List Bool) :
    gates base start (b :: bits) = gates base start bits ++
      [.mul (output start bits + 1) (output start bits) (output start bits),
        .mul (output start bits + 2) (output start bits + 1) (if b then base else start)] := by
  rw [gates, program, StraightLine.gates_append, next_eq]
  simp only [StraightLine.gates, Operation.gate, gates]

theorem gates_length (base start : ℕ) (bits : List Bool) :
    (gates base start bits).length = 2 * bits.length + 1 := by
  rw [gates, StraightLine.gates_length, program_length]

theorem constant_mem (base start : ℕ) (bits : List Bool) : Gate.constant start 1 ∈ gates base start bits := by
  induction bits with
  | nil => simp [gates_nil]
  | cons b bits ih => rw [gates_cons]; exact List.mem_append_left _ ih

theorem sound (base start : ℕ) (bits : List Bool) (env : ℕ → ℂ)
    (h : ∀ g ∈ gates base start bits, g.Holds env) :
    env (output start bits) = env base ^ Nat.fromBitsLE bits := by
  induction bits with
  | nil =>
    have hc := h (.constant start 1) (constant_mem base start [])
    simpa [Gate.Holds, output, Nat.fromBitsLE, Nat.fromBits] using hc
  | cons b bits ih =>
    have ht : ∀ g ∈ gates base start bits, g.Holds env := by
      intro g hg
      apply h g
      rw [gates_cons]
      exact List.mem_append_left _ hg
    have hp := ih ht
    have hc := h (.constant start 1) (constant_mem base start (b :: bits))
    have hs := h (.mul (output start bits + 1) (output start bits) (output start bits)) (by rw [gates_cons]; simp)
    have hf := h (.mul (output start bits + 2) (output start bits + 1) (if b then base else start)) (by rw [gates_cons]; simp)
    simp only [Gate.Holds, Int.cast_one] at hc hs hf
    rw [output_cons, hf, hs, hp]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ite_false, hc, mul_one, Nat.fromBitsLE_cons, Nat.zero_add]
      rw [show 2 * Nat.fromBitsLE bits = Nat.fromBitsLE bits + Nat.fromBitsLE bits by omega, pow_add]
    | true =>
      simp only [ite_true, Nat.fromBitsLE_cons]
      rw [show 1 + 2 * Nat.fromBitsLE bits = Nat.fromBitsLE bits + Nat.fromBitsLE bits + 1 by omega,
        pow_add, pow_add, pow_one]

theorem exists_completion (base start : ℕ) (hbase : base < start) (bits : List Bool) (env : ℕ → ℂ) :
    ∃ out : ℕ → ℂ, (∀ i < start, out i = env i) ∧ (∀ g ∈ gates base start bits, g.Holds out) ∧
      out (output start bits) = env base ^ Nat.fromBitsLE bits := by
  obtain ⟨out, hp, hg⟩ := StraightLine.exists_completion env start (program base start bits) (wellFormed base start hbase bits)
  refine ⟨out, hp, hg, ?_⟩
  rw [sound base start bits out hg, hp base hbase]

theorem gate_arity_le (base start : ℕ) (hbase : base < start) (bits : List Bool) (g : Gate)
    (hg : g ∈ gates base start bits) : g.arity ≤ output start bits + 1 := by
  have h := StraightLine.gates_arity start (program base start bits) (wellFormed base start hbase bits) g hg
  rwa [next_eq] at h

end LeanCanny.ETR.ComplexCircuit.Power
