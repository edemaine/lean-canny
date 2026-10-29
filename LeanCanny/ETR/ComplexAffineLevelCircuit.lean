/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineRow
public import LeanCanny.ETR.ComplexConstantTable

/-! # Shared ancestral level circuits

One uniform program computes a constant, a height at an earlier ambient
block, and the sum of heights at two earlier blocks. A tag selects the level
without duplicating any ancestral stage program.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineLevel
open scoped Classical BigOperators

structure Inputs where
  base : ℕ
  count : ℕ
  left : ℕ
  right : ℕ
  constant : ℤ
  normal : ℕ → ℤ
  mode : ℕ

structure Inputs.Valid (C : Inputs) : Prop where
  left : C.left + C.count ≤ C.base
  right : C.right + C.count ≤ C.base

def constantWire (C : Inputs) : ℕ := C.base + 1
def tableBase (C : Inputs) : ℕ := C.base + 2
def leftBase (C : Inputs) : ℕ := tableBase C + C.count
def rightBase (C : Inputs) : ℕ := leftBase C + AffineRow.stride C.count
def sumOutput (C : Inputs) : ℕ := rightBase C + AffineRow.stride C.count

def leftOutput (C : Inputs) : ℕ := AffineRow.output (leftBase C) C.count
def rightOutput (C : Inputs) : ℕ := AffineRow.output (rightBase C) C.count

def leftRow (C : Inputs) : List Operation :=
  AffineRow.height C.base (leftBase C) C.left C.count C.base (fun i => tableBase C + i)
def rightRow (C : Inputs) : List Operation :=
  AffineRow.height C.base (rightBase C) C.right C.count C.base (fun i => tableBase C + i)

def program (C : Inputs) : List Operation := .constant 0 :: .constant C.constant ::
  (ConstantTable.program C.count C.normal ++
    (leftRow C ++ (rightRow C ++ [.add (leftOutput C) (rightOutput C)])))

def gates (C : Inputs) : List Gate := StraightLine.gates C.base (program C)

def output (C : Inputs) : ℕ := if C.mode = 1 then leftOutput C else
  if C.mode = 2 then sumOutput C else constantWire C

theorem program_length (C : Inputs) : (program C).length = 9 * C.count + 9 := by
  simp only [program, List.length_cons, List.length_append, ConstantTable.program_length,
    leftRow, rightRow, AffineRow.height_length, List.length_nil, AffineRow.stride]
  omega

theorem gates_eq (C : Inputs) : gates C = .constant C.base 0 :: .constant (constantWire C) C.constant ::
    (StraightLine.gates (tableBase C) (ConstantTable.program C.count C.normal) ++
      (StraightLine.gates (leftBase C) (leftRow C) ++
        (StraightLine.gates (rightBase C) (rightRow C) ++ [.add (sumOutput C) (leftOutput C) (rightOutput C)]))) := by
  rw [gates, program, StraightLine.gates, StraightLine.gates, StraightLine.gates_append,
    ConstantTable.program_length, StraightLine.gates_append, leftRow, AffineRow.height_length,
    StraightLine.gates_append, rightRow, AffineRow.height_length]
  rfl

theorem wellFormed (C : Inputs) (h : C.Valid) : StraightLine.WellFormed C.base (program C) := by
  refine ⟨trivial, trivial, ?_⟩
  rw [StraightLine.wellFormed_append, ConstantTable.program_length]
  refine ⟨ConstantTable.wellFormed _ _ _, ?_⟩
  rw [StraightLine.wellFormed_append, leftRow, AffineRow.height_length]
  have hlbase : C.base < leftBase C := by unfold leftBase tableBase; omega
  have hrbase : C.base < rightBase C := by unfold rightBase leftBase tableBase; omega
  have hl : StraightLine.WellFormed (leftBase C) (leftRow C) :=
    AffineRow.height_wellFormed _ _ _ _ _ _ hlbase
      (fun i hi => by unfold leftBase; omega) (h.left.trans (by omega)) hlbase
  refine ⟨hl, ?_⟩
  rw [StraightLine.wellFormed_append, rightRow, AffineRow.height_length]
  have hr : StraightLine.WellFormed (rightBase C) (rightRow C) :=
    AffineRow.height_wellFormed _ _ _ _ _ _ hrbase
      (fun i hi => by unfold rightBase leftBase; omega) (h.right.trans (by omega)) hrbase
  refine ⟨hr, ?_⟩
  have hlout : leftOutput C < sumOutput C := by
    unfold leftOutput sumOutput rightBase AffineRow.output KernelRow.criticalWire AffineRow.stride
    omega
  have hrout : rightOutput C < sumOutput C := by
    unfold rightOutput sumOutput AffineRow.output KernelRow.criticalWire AffineRow.stride
    omega
  exact ⟨⟨hlout, hrout⟩, trivial⟩

theorem output_lt (C : Inputs) : output C < C.base + (program C).length := by
  rw [program_length]
  unfold output leftOutput sumOutput rightBase leftBase tableBase constantWire AffineRow.output KernelRow.criticalWire AffineRow.stride
  split_ifs <;> omega

end LeanCanny.ETR.ComplexCircuit.AffineLevel
