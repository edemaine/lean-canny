/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexGradientFamily
public import LeanCanny.ETR.ComplexKernelRowEncoding

/-! # Kernel circuits for a square block of shared polynomial outputs

The differentiated variables form a block inside the original input prefix.
Other inputs are frozen. The source program may compute additional guard
outputs alongside the square equations. Every Jacobian row shares the same
input assignment and normalized kernel vector, without sampling the roots.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SquareKernel
open MvPolynomial
open scoped Classical BigOperators

def zeroWire (start m : ℕ) : ℕ := start + m
def copyBase (start m : ℕ) : ℕ := zeroWire start m + 1
def rowBase (start m : ℕ) (ops : List Operation) : ℕ := copyBase start m + m * GradientFamily.stride start ops
def rowStart (start m : ℕ) (ops : List Operation) (j : ℕ) : ℕ := rowBase start m ops + j * (4 * m + 3)

def valueWire (start m : ℕ) (ops : List Operation) (out : ℕ) : ℕ :=
  GradientFamily.valueWire (copyBase start m) start ops 0 out

def entryWire (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (j k : ℕ) : ℕ :=
  GradientFamily.derivativeWire (copyBase start m) start ops k (outputs j)

def rowProgram (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (j : ℕ) : List Operation :=
  KernelRow.program (zeroWire start m) (rowStart start m ops j) start m
    (valueWire start m ops (outputs j)) (zeroWire start m) 0
    (fun _ => zeroWire start m) (entryWire start m ops outputs j)

def rowPrefix (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) : ℕ → List Operation
  | 0 => []
  | count + 1 => rowPrefix start m ops outputs count ++ rowProgram start m ops outputs count

def rowGates (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) : List Gate :=
  StraightLine.gates (rowBase start m ops) (rowPrefix start m ops outputs count)

def program (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) : List Operation :=
  [.constant 0] ++ (GradientFamily.program (zeroWire start m) (copyBase start m) start offset ops m ++
    rowPrefix start m ops outputs m)

def equationWire (start m : ℕ) (ops : List Operation) (j : ℕ) : ℕ :=
  KernelRow.criticalWire (rowStart start m ops j) m

def kernelWire (start m : ℕ) (ops : List Operation) (j : ℕ) : ℕ :=
  KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m

theorem rowPrefix_length (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) :
    (rowPrefix start m ops outputs count).length = count * (4 * m + 3) := by
  induction count with
  | zero => simp only [rowPrefix, List.length_nil, Nat.zero_mul]
  | succ count ih =>
    simp only [rowPrefix, List.length_append, rowProgram, KernelRow.program_length, ih, Nat.succ_mul]

theorem rowPrefix_next (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) :
    rowBase start m ops + (rowPrefix start m ops outputs count).length = rowStart start m ops count := by
  rw [rowPrefix_length]
  rfl

theorem rowGates_succ (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) :
    rowGates start m ops outputs (count + 1) = rowGates start m ops outputs count ++
      StraightLine.gates (rowStart start m ops count) (rowProgram start m ops outputs count) := by
  rw [rowGates, rowPrefix, StraightLine.gates_append, rowPrefix_next]
  rfl

theorem rowGates_range (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) :
    rowGates start m ops outputs count = (List.range count).flatMap (fun j =>
      StraightLine.gates (rowStart start m ops j) (rowProgram start m ops outputs j)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [rowGates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gates_eq (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) :
    StraightLine.gates (zeroWire start m) (program start m offset ops outputs) =
      [.constant (zeroWire start m) 0] ++
        (GradientFamily.gates (zeroWire start m) (copyBase start m) start offset ops m ++ rowGates start m ops outputs m) := by
  rw [program, StraightLine.gates_append]
  change [.constant (zeroWire start m) 0] ++
    StraightLine.gates (copyBase start m) (GradientFamily.program (zeroWire start m) (copyBase start m)
      start offset ops m ++ rowPrefix start m ops outputs m) = _
  rw [StraightLine.gates_append, GradientFamily.program_length]
  rfl

theorem program_length (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) :
    (program start m offset ops outputs).length =
      1 + m * GradientFamily.stride start ops + m * (4 * m + 3) := by
  simp only [program, List.length_append, List.length_cons, List.length_nil,
    GradientFamily.program_length, rowPrefix_length]
  omega

theorem row_wellFormed (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (j : ℕ)
    (hj : j < m) (ho : outputs j < start + ops.length) :
    StraightLine.WellFormed (rowStart start m ops j) (rowProgram start m ops outputs j) := by
  have hb : rowBase start m ops ≤ rowStart start m ops j := by unfold rowStart; omega
  have hz : zeroWire start m < rowStart start m ops j := by
    unfold rowBase copyBase at hb
    omega
  apply KernelRow.wellFormed (zeroWire start m) _ start m _ (zeroWire start m) 0
    (fun _ => zeroWire start m) (entryWire start m ops outputs j) hz (fun _ _ => hz) ?_ ?_ ?_ hz
  · intro k hk
    exact (GradientFamily.derivativeWire_lt_end (copyBase start m) start ops m k (outputs j) hk ho).trans_le hb
  · unfold zeroWire at hz
    omega
  · exact (GradientFamily.valueWire_lt_end (copyBase start m) start ops m 0 (outputs j) (by omega) ho).trans_le hb

theorem rowPrefix_wellFormed (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (ho : ∀ j < m, outputs j < start + ops.length) (count : ℕ) (hc : count ≤ m) :
    StraightLine.WellFormed (rowBase start m ops) (rowPrefix start m ops outputs count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [rowPrefix, StraightLine.wellFormed_append, rowPrefix_next]
    exact ⟨ih (by omega), row_wellFormed start m ops outputs count (by omega) (ho count (by omega))⟩

theorem wellFormed (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hw : StraightLine.WellFormed start ops) (ho : ∀ j < m, outputs j < start + ops.length) :
    StraightLine.WellFormed (zeroWire start m) (program start m offset ops outputs) := by
  rw [program, StraightLine.wellFormed_append]
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  change StraightLine.WellFormed (copyBase start m)
    (GradientFamily.program (zeroWire start m) (copyBase start m) start offset ops m ++ rowPrefix start m ops outputs m)
  rw [StraightLine.wellFormed_append, GradientFamily.program_length]
  exact ⟨GradientFamily.wellFormed _ _ _ _ ops m (by unfold copyBase; omega)
    (by unfold copyBase zeroWire; omega) hw, rowPrefix_wellFormed start m ops outputs ho m le_rfl⟩

theorem zero_sound (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m offset ops outputs), g.Holds env) :
    env (zeroWire start m) = 0 := by
  have H := hg (.constant (zeroWire start m) 0) (by rw [gates_eq]; simp)
  simpa only [Gate.Holds, Int.cast_zero] using H

theorem jet_sound (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m offset ops outputs), g.Holds env)
    (k : ℕ) (hk : k < m) (out : ℕ) (ho : out < start + ops.length) :
    env (GradientFamily.valueWire (copyBase start m) start ops k out) = (wire out).eval₂ (Int.castRingHom ℂ) x ∧
      env (GradientFamily.derivativeWire (copyBase start m) start ops k out) =
        (pderiv (offset + k) (wire out)).eval₂ (Int.castRingHom ℂ) x := by
  apply GradientFamily.sound wire (zeroWire start m) (copyBase start m) start offset ops hw hr hin x env
    (zero_sound start m offset ops outputs env hg) hx m ?_ k hk out ho
  intro g h
  exact hg g (by rw [gates_eq]; exact List.mem_append_right _ (List.mem_append_left _ h))

theorem rows_sound (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : ∀ j < m, outputs j < start + ops.length)
    (x u env : ℕ → ℂ) (hx : ∀ i < start, env i = x i) (hu : ∀ k < m, env (start + k) = u k)
    (hg : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m offset ops outputs), g.Holds env)
    (j : ℕ) (hj : j < m) :
    env (equationWire start m ops j) = (wire (outputs j)).eval₂ (Int.castRingHom ℂ) x ∧
      env (kernelWire start m ops j) = ∑ k ∈ Finset.range m,
        (pderiv (offset + k) (wire (outputs j))).eval₂ (Int.castRingHom ℂ) x * u k := by
  have hrow : ∀ g ∈ StraightLine.gates (rowStart start m ops j) (rowProgram start m ops outputs j), g.Holds env := by
    intro g h
    apply hg g
    rw [gates_eq]
    apply List.mem_append_right
    apply List.mem_append_right
    rw [rowGates_range]
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, h⟩
  have H := KernelRow.sound (zeroWire start m) (rowStart start m ops j) start m
    (valueWire start m ops (outputs j)) (zeroWire start m) 0 (fun _ => zeroWire start m)
    (entryWire start m ops outputs j) env (zero_sound start m offset ops outputs env hg) hrow
  simp only [Int.cast_zero, zero_mul, add_zero] at H
  have hv := (jet_sound wire start m offset ops outputs hw hr hin x env hx hg 0 (by omega) (outputs j) (ho j hj)).1
  refine ⟨H.2.trans hv, H.1.trans ?_⟩
  apply Finset.sum_congr rfl
  intro k hk
  change env (GradientFamily.derivativeWire (copyBase start m) start ops k (outputs j)) * env (start + k) = _
  rw [(jet_sound wire start m offset ops outputs hw hr hin x env hx hg k
    (Finset.mem_range.mp hk) (outputs j) (ho j hj)).2, hu k (Finset.mem_range.mp hk)]

end LeanCanny.ETR.ComplexCircuit.SquareKernel
