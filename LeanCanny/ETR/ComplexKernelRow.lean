/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexStraightLine
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Shared arithmetic for one critical Jacobian-kernel row

The row forms a linear combination of two Hessian rows, multiplies by the
kernel coordinates, and accumulates the result. A separate output forms the
corresponding critical equation from the selected first derivatives.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.KernelRow
open scoped Classical BigOperators

def sumWire (zWire start : ℕ) (k : ℕ) : ℕ := if k = 0 then zWire else start + 4 * k
def stepStart (start k : ℕ) : ℕ := start + 1 + 4 * k
def criticalWire (start m : ℕ) : ℕ := start + 4 * m + 2

def step (zWire start kernelStart : ℕ) (first entry : ℕ → ℕ) (k : ℕ) : List Operation :=
  [.mul start (first k), .add (entry k) (stepStart start k),
    .mul (stepStart start k + 1) (kernelStart + k),
    .add (sumWire zWire start k) (stepStart start k + 2)]

def stepGates (zWire start kernelStart : ℕ) (first entry : ℕ → ℕ) (k : ℕ) : List Gate :=
  [.mul (stepStart start k) start (first k),
    .add (stepStart start k + 1) (entry k) (stepStart start k),
    .mul (stepStart start k + 2) (stepStart start k + 1) (kernelStart + k),
    .add (sumWire zWire start (k + 1)) (sumWire zWire start k) (stepStart start k + 2)]

def prefixProgram (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) : ℕ → List Operation
  | 0 => [.constant coefficient]
  | k + 1 => prefixProgram zWire start kernelStart coefficient first entry k ++ step zWire start kernelStart first entry k

def prefixGates (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) (m : ℕ) : List Gate :=
  StraightLine.gates start (prefixProgram zWire start kernelStart coefficient first entry m)

def program (zWire start kernelStart m value baseGradient : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) : List Operation :=
  prefixProgram zWire start kernelStart coefficient first entry m ++
    [.mul start baseGradient, .add value (start + 4 * m + 1)]

theorem prefix_length (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) (m : ℕ) :
    (prefixProgram zWire start kernelStart coefficient first entry m).length = 1 + 4 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prefixProgram, List.length_append, step, List.length_cons, List.length_nil, ih]
    omega

theorem program_length (zWire start kernelStart m value baseGradient : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) :
    (program zWire start kernelStart m value baseGradient coefficient first entry).length = 4 * m + 3 := by
  simp only [program, List.length_append, prefix_length, List.length_cons, List.length_nil]
  omega

theorem step_gates_eq (zWire start kernelStart : ℕ) (first entry : ℕ → ℕ) (k : ℕ) :
    StraightLine.gates (stepStart start k) (step zWire start kernelStart first entry k) =
      stepGates zWire start kernelStart first entry k := by
  have ho : stepStart start k + 3 = sumWire zWire start (k + 1) := by
    simp only [stepStart, sumWire, Nat.add_one_ne_zero, ite_false]
    omega
  simp only [step, StraightLine.gates, Operation.gate, stepGates]
  rw [ho]

theorem prefixGates_succ (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) (m : ℕ) :
    prefixGates zWire start kernelStart coefficient first entry (m + 1) =
      prefixGates zWire start kernelStart coefficient first entry m ++ stepGates zWire start kernelStart first entry m := by
  rw [prefixGates, prefixProgram, StraightLine.gates_append, prefix_length]
  rw [show start + (1 + 4 * m) = stepStart start m by unfold stepStart; omega, step_gates_eq]
  rfl

theorem prefixGates_range (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) (m : ℕ) :
    prefixGates zWire start kernelStart coefficient first entry m =
      [.constant start coefficient] ++ (List.range m).flatMap (stepGates zWire start kernelStart first entry) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [prefixGates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem gates_eq (zWire start kernelStart m value baseGradient : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) :
    StraightLine.gates start (program zWire start kernelStart m value baseGradient coefficient first entry) =
      prefixGates zWire start kernelStart coefficient first entry m ++
        [.mul (start + 4 * m + 1) start baseGradient,
          .add (criticalWire start m) value (start + 4 * m + 1)] := by
  rw [program, StraightLine.gates_append, prefix_length]
  rw [show start + (1 + 4 * m) = start + 4 * m + 1 by omega]
  simp only [StraightLine.gates, Operation.gate, criticalWire, prefixGates]

theorem step_wellFormed (zWire start kernelStart : ℕ) (first entry : ℕ → ℕ) (k : ℕ)
    (hz : zWire < start) (hf : first k < start) (he : entry k < start) (hu : kernelStart + k < start) :
    StraightLine.WellFormed (stepStart start k) (step zWire start kernelStart first entry k) := by
  have hs : sumWire zWire start k < stepStart start k := by
    unfold sumWire stepStart
    split_ifs <;> omega
  simp only [step, StraightLine.WellFormed, Operation.InputsBelow]
  unfold stepStart at *
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem prefix_wellFormed (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ)
    (m : ℕ) (hz : zWire < start) (hf : ∀ k < m, first k < start)
    (he : ∀ k < m, entry k < start) (hu : kernelStart + m ≤ start) :
    StraightLine.WellFormed start (prefixProgram zWire start kernelStart coefficient first entry m) := by
  induction m with
  | zero => exact ⟨trivial, trivial⟩
  | succ m ih =>
    rw [prefixProgram, StraightLine.wellFormed_append, prefix_length]
    have hp := ih (fun k hk => hf k (by omega)) (fun k hk => he k (by omega)) (by omega)
    refine ⟨hp, ?_⟩
    rw [show start + (1 + 4 * m) = stepStart start m by unfold stepStart; omega]
    exact step_wellFormed zWire start kernelStart first entry m hz (hf m (by omega)) (he m (by omega)) (by omega)

theorem wellFormed (zWire start kernelStart m value baseGradient : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ)
    (hz : zWire < start) (hf : ∀ k < m, first k < start) (he : ∀ k < m, entry k < start)
    (hu : kernelStart + m ≤ start) (hv : value < start) (hb : baseGradient < start) :
    StraightLine.WellFormed start (program zWire start kernelStart m value baseGradient coefficient first entry) := by
  rw [program, StraightLine.wellFormed_append, prefix_length]
  refine ⟨prefix_wellFormed zWire start kernelStart coefficient first entry m hz hf he hu, ?_⟩
  simp only [StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem prefix_sound (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ)
    (m : ℕ) (env : ℕ → ℂ) (hz : env zWire = 0)
    (hg : ∀ g ∈ prefixGates zWire start kernelStart coefficient first entry m, g.Holds env) :
    env start = coefficient ∧ env (sumWire zWire start m) =
      ∑ k ∈ Finset.range m, (env (entry k) + (coefficient : ℂ) * env (first k)) * env (kernelStart + k) := by
  induction m with
  | zero =>
    exact ⟨hg (.constant start coefficient) (by simp [prefixGates, prefixProgram, StraightLine.gates, Operation.gate]),
      by simpa only [sumWire, ite_true, Finset.sum_range_zero] using hz⟩
  | succ m ih =>
    have hp : ∀ g ∈ prefixGates zWire start kernelStart coefficient first entry m, g.Holds env := by
      intro g h
      exact hg g (by rw [prefixGates_succ]; exact List.mem_append_left _ h)
    have hs : ∀ g ∈ stepGates zWire start kernelStart first entry m, g.Holds env := by
      intro g h
      exact hg g (by rw [prefixGates_succ]; exact List.mem_append_right _ h)
    have hm := hs (.mul (stepStart start m) start (first m)) (by simp [stepGates])
    have ha := hs (.add (stepStart start m + 1) (entry m) (stepStart start m)) (by simp [stepGates])
    have hu := hs (.mul (stepStart start m + 2) (stepStart start m + 1) (kernelStart + m)) (by simp [stepGates])
    have ht := hs (.add (sumWire zWire start (m + 1)) (sumWire zWire start m) (stepStart start m + 2)) (by simp [stepGates])
    simp only [Gate.Holds] at hm ha hu ht
    obtain ⟨hc, hv⟩ := ih hp
    exact ⟨hc, by rw [ht, hu, ha, hm, hc, hv, Finset.sum_range_succ]⟩

theorem sound (zWire start kernelStart m value baseGradient : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ)
    (env : ℕ → ℂ) (hz : env zWire = 0)
    (hg : ∀ g ∈ StraightLine.gates start (program zWire start kernelStart m value baseGradient coefficient first entry), g.Holds env) :
    env (sumWire zWire start m) =
      ∑ k ∈ Finset.range m, (env (entry k) + (coefficient : ℂ) * env (first k)) * env (kernelStart + k) ∧
    env (criticalWire start m) = env value + (coefficient : ℂ) * env baseGradient := by
  have hp : ∀ g ∈ prefixGates zWire start kernelStart coefficient first entry m, g.Holds env := by
    intro g h
    exact hg g (by rw [gates_eq]; exact List.mem_append_left _ h)
  have hm := hg (.mul (start + 4 * m + 1) start baseGradient) (by rw [gates_eq]; simp)
  have ha := hg (.add (criticalWire start m) value (start + 4 * m + 1)) (by rw [gates_eq]; simp)
  simp only [Gate.Holds] at hm ha
  obtain ⟨hc, hs⟩ := prefix_sound zWire start kernelStart coefficient first entry m env hz hp
  exact ⟨hs, by rw [ha, hm, hc]⟩

end LeanCanny.ETR.ComplexCircuit.KernelRow
