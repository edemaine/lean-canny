/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexStraightLine
public import LeanCanny.ETR.EncodingBounds

/-! # Acyclic shared circuits for source arithmetic expressions

Constants and arithmetic nodes allocate one fresh wire each. Variables refer
to existing input wires. The compiler preserves the complete complex value of
the original term, and every input assignment has a satisfying completion.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source
open scoped Classical

def count : Term → ℕ
  | .const _ => 1
  | .var _ => 0
  | .add a b | .mul a b => count a + count b + 1

def output (start : ℕ) : Term → ℕ
  | .const _ => start
  | .var i => i
  | .add a b | .mul a b => start + count a + count b

def program (start : ℕ) : Term → List Operation
  | .const z => [.constant z]
  | .var _ => []
  | .add a b => program start a ++ program (start + count a) b ++
      [.add (output start a) (output (start + count a) b)]
  | .mul a b => program start a ++ program (start + count a) b ++
      [.mul (output start a) (output (start + count a) b)]

def gates (start : ℕ) : Term → List Gate
  | .const z => [.constant start z]
  | .var _ => []
  | .add a b => gates start a ++ gates (start + count a) b ++
      [.add (output start (.add a b)) (output start a) (output (start + count a) b)]
  | .mul a b => gates start a ++ gates (start + count a) b ++
      [.mul (output start (.mul a b)) (output start a) (output (start + count a) b)]

theorem program_length (start : ℕ) (t : Term) : (program start t).length = count t := by
  induction t generalizing start with
  | const z => rfl
  | var i => rfl
  | add a b ha hb => simp only [program, count, List.length_append, List.length_cons, List.length_nil, ha, hb]
  | mul a b ha hb => simp only [program, count, List.length_append, List.length_cons, List.length_nil, ha, hb]

theorem gates_eq (start : ℕ) (t : Term) : StraightLine.gates start (program start t) = gates start t := by
  induction t generalizing start with
  | const z => rfl
  | var i => rfl
  | add a b ha hb =>
    simp only [program, StraightLine.gates_append, List.length_append, program_length,
      StraightLine.gates, Operation.gate, ha, hb, gates, output, Nat.add_assoc]
  | mul a b ha hb =>
    simp only [program, StraightLine.gates_append, List.length_append, program_length,
      StraightLine.gates, Operation.gate, ha, hb, gates, output, Nat.add_assoc]

theorem output_lt (start : ℕ) (t : Term) (ht : t.arity ≤ start) : output start t < start + count t := by
  cases t <;> simp only [output, count, Term.arity] at * <;> omega

theorem wellFormed (start : ℕ) (t : Term) (ht : t.arity ≤ start) :
    StraightLine.WellFormed start (program start t) := by
  induction t generalizing start with
  | const z => exact ⟨trivial, trivial⟩
  | var i => trivial
  | add a b ha hb =>
    have hA : a.arity ≤ start := (Nat.le_max_left ..).trans ht
    have hB : b.arity ≤ start + count a := (Nat.le_max_right ..).trans (ht.trans (Nat.le_add_right ..))
    have hoA := output_lt start a hA
    have hoB := output_lt (start + count a) b hB
    rw [program, StraightLine.wellFormed_append, StraightLine.wellFormed_append]
    refine ⟨⟨ha start hA, ?_⟩, ?_⟩
    · simpa only [program_length] using hb (start + count a) hB
    · simp only [List.length_append, program_length, StraightLine.WellFormed, Operation.InputsBelow]
      exact ⟨⟨by omega, by omega⟩, trivial⟩
  | mul a b ha hb =>
    have hA : a.arity ≤ start := (Nat.le_max_left ..).trans ht
    have hB : b.arity ≤ start + count a := (Nat.le_max_right ..).trans (ht.trans (Nat.le_add_right ..))
    have hoA := output_lt start a hA
    have hoB := output_lt (start + count a) b hB
    rw [program, StraightLine.wellFormed_append, StraightLine.wellFormed_append]
    refine ⟨⟨ha start hA, ?_⟩, ?_⟩
    · simpa only [program_length] using hb (start + count a) hB
    · simp only [List.length_append, program_length, StraightLine.WellFormed, Operation.InputsBelow]
      exact ⟨⟨by omega, by omega⟩, trivial⟩

theorem sound (start : ℕ) (t : Term) (env : ℕ → ℂ)
    (h : ∀ g ∈ gates start t, g.Holds env) : env (output start t) = t.eval env := by
  induction t generalizing start with
  | const z => exact h (.constant start z) (by simp [gates])
  | var i => rfl
  | add a b ha hb =>
    have hA : ∀ g ∈ gates start a, g.Holds env := by
      intro g hg; exact h g (by simp only [gates, List.mem_append]; exact Or.inl (Or.inl hg))
    have hB : ∀ g ∈ gates (start + count a) b, g.Holds env := by
      intro g hg; exact h g (by simp only [gates, List.mem_append]; exact Or.inl (Or.inr hg))
    have ho := h (.add (output start (.add a b)) (output start a) (output (start + count a) b)) (by simp [gates])
    exact ho.trans (congrArg₂ (· + ·) (ha start hA) (hb _ hB))
  | mul a b ha hb =>
    have hA : ∀ g ∈ gates start a, g.Holds env := by
      intro g hg; exact h g (by simp only [gates, List.mem_append]; exact Or.inl (Or.inl hg))
    have hB : ∀ g ∈ gates (start + count a) b, g.Holds env := by
      intro g hg; exact h g (by simp only [gates, List.mem_append]; exact Or.inl (Or.inr hg))
    have ho := h (.mul (output start (.mul a b)) (output start a) (output (start + count a) b)) (by simp [gates])
    exact ho.trans (congrArg₂ (· * ·) (ha start hA) (hb _ hB))

theorem exists_completion (start : ℕ) (t : Term) (ht : t.arity ≤ start) (env : ℕ → ℂ) :
    ∃ out : ℕ → ℂ, (∀ i < start, out i = env i) ∧ (∀ g ∈ gates start t, g.Holds out) ∧
      out (output start t) = t.eval env := by
  obtain ⟨out, hp, hg⟩ := StraightLine.exists_completion env start (program start t) (wellFormed start t ht)
  rw [gates_eq] at hg
  refine ⟨out, hp, hg, (sound start t out hg).trans ?_⟩
  exact t.eval_congr out env (fun i hi => hp i (hi.trans_le ht))

theorem gates_length (start : ℕ) (t : Term) : (gates start t).length = count t := by
  rw [← gates_eq, StraightLine.gates_length, program_length]

theorem gate_arity_le (start : ℕ) (t : Term) (ht : t.arity ≤ start) (g : Gate) (hg : g ∈ gates start t) :
    g.arity ≤ start + count t := by
  rw [← gates_eq] at hg
  have h := StraightLine.gates_arity start (program start t) (wellFormed start t ht) g hg
  simpa only [program_length] using h

theorem count_le_dataSize (t : Term) : count t ≤ t.toData.size := by
  induction t with
  | const z => exact @Data.size_pos (Term.const z).toData
  | var i => exact Nat.zero_le _
  | add a b ha hb => simp only [count, Term.dataSize_add]; omega
  | mul a b ha hb => simp only [count, Term.dataSize_mul]; omega

end LeanCanny.ETR.ComplexCircuit.Source
