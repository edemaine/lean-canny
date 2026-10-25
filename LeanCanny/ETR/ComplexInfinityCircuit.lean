/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexPowerCircuit

/-! # Shared power and sum circuits for critical roots at infinity

One block per input coordinate computes its `(N-1)`st and `N`th powers, updates
the power sum, and forms its critical-direction difference. The exponent is
supplied in binary; each block has two operations per bit plus six operations.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Infinity
open scoped Classical

def stride (bits : List Bool) : ℕ := 2 * bits.length + 6
def start (m : ℕ) (bits : List Bool) (j : ℕ) : ℕ := m + 1 + j * stride bits
def powerWire (m : ℕ) (bits : List Bool) (j : ℕ) : ℕ := start m bits j + 2 * bits.length
def sumWire (m : ℕ) (bits : List Bool) : ℕ → ℕ
  | 0 => m
  | j + 1 => powerWire m bits j + 2
def differenceWire (m : ℕ) (bits : List Bool) (j : ℕ) : ℕ := powerWire m bits j + 5

def block (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) : List Operation :=
  Power.program j (start m bits j) bits ++
    [.mul (powerWire m bits j) j,
      .add (sumWire m bits j) (powerWire m bits j + 1),
      .constant (-v j), .mul (powerWire m bits j + 3) (powerWire m bits 0),
      .add (powerWire m bits j) (powerWire m bits j + 4)]

def blockGates (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) : List Gate :=
  Power.gates j (start m bits j) bits ++
    [.mul (powerWire m bits j + 1) (powerWire m bits j) j,
      .add (sumWire m bits (j + 1)) (sumWire m bits j) (powerWire m bits j + 1),
      .constant (powerWire m bits j + 3) (-v j),
      .mul (powerWire m bits j + 4) (powerWire m bits j + 3) (powerWire m bits 0),
      .add (differenceWire m bits j) (powerWire m bits j) (powerWire m bits j + 4)]

def prefixProgram (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) : ℕ → List Operation
  | 0 => [.constant 0]
  | k + 1 => prefixProgram m bits v k ++ block m bits v k

def prefixGates (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) : List Gate :=
  StraightLine.gates m (prefixProgram m bits v k)

theorem start_succ (m : ℕ) (bits : List Bool) (j : ℕ) :
    start m bits (j + 1) = start m bits j + stride bits := by
  simp only [start, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem power_eq (m : ℕ) (bits : List Bool) (j : ℕ) :
    Power.output (start m bits j) bits = powerWire m bits j := rfl

theorem sumWire_lt_start (m : ℕ) (bits : List Bool) (j : ℕ) : sumWire m bits j < start m bits j := by
  cases j with
  | zero => simp [sumWire, start]
  | succ j => rw [sumWire, start_succ]; unfold powerWire stride; omega

theorem base_power_le (m : ℕ) (bits : List Bool) (j : ℕ) : powerWire m bits 0 ≤ powerWire m bits j := by
  unfold powerWire start
  omega

theorem block_length (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) :
    (block m bits v j).length = stride bits := by
  simp only [block, List.length_append, Power.program_length, List.length_cons, List.length_nil, stride]

theorem prefix_length (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) :
    (prefixProgram m bits v k).length = 1 + k * stride bits := by
  induction k with
  | zero => simp [prefixProgram]
  | succ k ih => simp only [prefixProgram, List.length_append, block_length, ih, Nat.succ_mul]; omega

theorem prefix_next (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) :
    m + (prefixProgram m bits v k).length = start m bits k := by rw [prefix_length]; simp [start, Nat.add_assoc]

theorem block_gates_eq (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) :
    StraightLine.gates (start m bits j) (block m bits v j) = blockGates m bits v j := by
  rw [block, StraightLine.gates_append, Power.next_eq, power_eq]
  simp only [StraightLine.gates, Operation.gate, blockGates, sumWire, differenceWire, Power.gates]

theorem prefixGates_zero (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) :
    prefixGates m bits v 0 = [.constant m 0] := rfl

theorem prefixGates_succ (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) :
    prefixGates m bits v (k + 1) = prefixGates m bits v k ++ blockGates m bits v k := by
  rw [prefixGates, prefixProgram, StraightLine.gates_append, prefix_next, block_gates_eq]
  rfl

theorem block_wellFormed (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) (hj : j < m) :
    StraightLine.WellFormed (start m bits j) (block m bits v j) := by
  have hbase : j < start m bits j := by unfold start; omega
  have hsum := sumWire_lt_start m bits j
  have hpower := base_power_le m bits j
  rw [block, StraightLine.wellFormed_append, Power.next_eq, power_eq]
  refine ⟨Power.wellFormed _ _ hbase bits, ?_⟩
  simp only [StraightLine.WellFormed, Operation.InputsBelow]
  have hstart : start m bits j ≤ powerWire m bits j := by unfold powerWire; omega
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem wellFormed (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) (hk : k ≤ m) :
    StraightLine.WellFormed m (prefixProgram m bits v k) := by
  induction k with
  | zero => exact ⟨trivial, trivial⟩
  | succ k ih =>
    rw [prefixProgram, StraightLine.wellFormed_append, prefix_next]
    exact ⟨ih (by omega), block_wellFormed m bits v k (by omega)⟩

theorem block_mem_prefix (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k j : ℕ) (hj : j < k)
    (g : Gate) (hg : g ∈ blockGates m bits v j) : g ∈ prefixGates m bits v k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [prefixGates_succ]
    by_cases hlt : j < k
    · exact List.mem_append_left _ (ih hlt)
    · have he : j = k := by omega
      exact List.mem_append_right _ (by simpa only [he] using hg)

end LeanCanny.ETR.ComplexCircuit.Infinity
