/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexHessianFamily
public import LeanCanny.ETR.ComplexKernelRowEncoding

/-! # One shared circuit for normalized affine critical kernels

The original coordinates and kernel coordinates precede a shared zero wire.
A full family of Hessian copies follows, then one arithmetic block per matrix
row. The final constraints normalize the kernel and set both row outputs to
zero. All computation before those constraints is one acyclic program.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open scoped Classical

def zeroWire (start m : ℕ) : ℕ := start + m
def copyBase (start m : ℕ) : ℕ := zeroWire start m + 1
def rowStride (m : ℕ) : ℕ := 4 * m + 3
def rowsBase (start m : ℕ) (ops : List Operation) : ℕ :=
  HessianFamily.blockStart (copyBase start m) start ops (m * m)
def rowStart (start m : ℕ) (ops : List Operation) (j : ℕ) : ℕ := rowsBase start m ops + j * rowStride m

def jetWire (start m : ℕ) (ops : List Operation) (out j k slot : ℕ) : ℕ :=
  HessianFamily.blockStart (copyBase start m) start ops (j * m + k) + 16 * out + slot
def valueWire (start m : ℕ) (ops : List Operation) (out : ℕ) : ℕ := jetWire start m ops out 0 0 0
def gradientWire (start m : ℕ) (ops : List Operation) (out k : ℕ) : ℕ := jetWire start m ops out 0 k 3
def hessianWire (start m : ℕ) (ops : List Operation) (out j k : ℕ) : ℕ := jetWire start m ops out j k 15

def coefficient (v : ℕ → ℤ) (j : ℕ) : ℤ := if j = 0 then 0 else -v (j - 1)
def selectedValue (start m : ℕ) (ops : List Operation) (out j : ℕ) : ℕ :=
  if j = 0 then valueWire start m ops out else gradientWire start m ops out j
def entry (start m : ℕ) (ops : List Operation) (out j k : ℕ) : ℕ :=
  if j = 0 then gradientWire start m ops out k else hessianWire start m ops out j k

def row (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (j : ℕ) : List Operation :=
  KernelRow.program (zeroWire start m) (rowStart start m ops j) start m
    (selectedValue start m ops out j) (gradientWire start m ops out 0) (coefficient v j)
    (hessianWire start m ops out 0) (entry start m ops out j)

def rowsProgram (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) : ℕ → List Operation
  | 0 => []
  | j + 1 => rowsProgram start m ops out v j ++ row start m ops out v j

def prefixProgram (start m : ℕ) (ops : List Operation) : List Operation :=
  [.constant 0] ++ HessianFamily.program (zeroWire start m) (copyBase start m) start m ops (m * m)
def program (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) : List Operation :=
  prefixProgram start m ops ++ rowsProgram start m ops out v m

def constraints (start m : ℕ) (ops : List Operation) (chart : ℕ) : List Gate :=
  [.constant (start + chart) 1] ++ (List.range m).flatMap (fun j =>
    [.zero (KernelRow.sumWire (zeroWire start m) (rowStart start m ops j) m),
      .zero (KernelRow.criticalWire (rowStart start m ops j) m)])
def query (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (chart : ℕ) : List Gate :=
  StraightLine.gates (zeroWire start m) (program start m ops out v) ++ constraints start m ops chart

theorem jetWire_lt_rows (start m : ℕ) (ops : List Operation) (out j k slot : ℕ)
    (ho : out < start + ops.length) (hj : j < m) (hk : k < m) (hslot : slot < 16) :
    jetWire start m ops out j k slot < rowsBase start m ops := by
  have hq : j * m + k < m * m := by nlinarith
  have hb : 16 * out + slot < HessianFamily.stride start ops := by unfold HessianFamily.stride; omega
  have ht := Nat.mul_le_mul_right (HessianFamily.stride start ops) (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at ht
  unfold jetWire rowsBase HessianFamily.blockStart
  omega

theorem row_length (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (j : ℕ) :
    (row start m ops out v j).length = rowStride m := KernelRow.program_length _ _ _ _ _ _ _ _ _

theorem rows_length (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (count : ℕ) :
    (rowsProgram start m ops out v count).length = count * rowStride m := by
  induction count with
  | zero => simp only [rowsProgram, List.length_nil, Nat.zero_mul]
  | succ count ih => rw [rowsProgram, List.length_append, row_length, ih, Nat.succ_mul]

theorem prefix_next (start m : ℕ) (ops : List Operation) :
    zeroWire start m + (prefixProgram start m ops).length = rowsBase start m ops := by
  simp only [prefixProgram, List.length_append, List.length_cons, List.length_nil, HessianFamily.program_length,
    rowsBase, HessianFamily.blockStart, copyBase]
  omega

theorem rows_next (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (count : ℕ) :
    rowsBase start m ops + (rowsProgram start m ops out v count).length = rowStart start m ops count := by
  rw [rows_length]
  rfl

theorem row_wellFormed (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (j : ℕ)
    (ho : out < start + ops.length) (hj : j < m) :
    StraightLine.WellFormed (rowStart start m ops j) (row start m ops out v j) := by
  have hm : 0 < m := by omega
  have hr : rowsBase start m ops ≤ rowStart start m ops j := by unfold rowStart; omega
  have hz : zeroWire start m < rowsBase start m ops := by
    unfold rowsBase HessianFamily.blockStart copyBase; omega
  have hgrad (k : ℕ) (hk : k < m) : gradientWire start m ops out k < rowStart start m ops j :=
    (jetWire_lt_rows start m ops out 0 k 3 ho hm hk (by decide)).trans_le hr
  have hhess (j' k : ℕ) (hj' : j' < m) (hk : k < m) :
      hessianWire start m ops out j' k < rowStart start m ops j :=
    (jetWire_lt_rows start m ops out j' k 15 ho hj' hk (by decide)).trans_le hr
  unfold row
  apply KernelRow.wellFormed
  · exact hz.trans_le hr
  · exact fun k hk => hhess 0 k hm hk
  · intro k hk
    unfold entry
    split_ifs
    · exact hgrad k hk
    · exact hhess j k hj hk
  · unfold zeroWire at hz; omega
  · unfold selectedValue
    split_ifs
    · exact (jetWire_lt_rows start m ops out 0 0 0 ho hm hm (by decide)).trans_le hr
    · exact hgrad j hj
  · exact hgrad 0 hm

theorem rows_wellFormed (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ)
    (ho : out < start + ops.length) (count : ℕ) (hc : count ≤ m) :
    StraightLine.WellFormed (rowsBase start m ops) (rowsProgram start m ops out v count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [rowsProgram, StraightLine.wellFormed_append, rows_next]
    exact ⟨ih (by omega), row_wellFormed start m ops out v count ho (by omega)⟩

theorem wellFormed (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ)
    (hw : StraightLine.WellFormed start ops) (ho : out < start + ops.length) :
    StraightLine.WellFormed (zeroWire start m) (program start m ops out v) := by
  rw [program, StraightLine.wellFormed_append, prefix_next]
  refine ⟨?_, rows_wellFormed start m ops out v ho m le_rfl⟩
  rw [prefixProgram, StraightLine.wellFormed_append]
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  change StraightLine.WellFormed (copyBase start m)
    (HessianFamily.program (zeroWire start m) (copyBase start m) start m ops (m * m))
  exact HessianFamily.wellFormed _ _ _ _ _ _ (by unfold copyBase; omega)
    (by unfold copyBase zeroWire; omega) hw

theorem rows_gates_range (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (count : ℕ) :
    StraightLine.gates (rowsBase start m ops) (rowsProgram start m ops out v count) =
      (List.range count).flatMap (fun j => StraightLine.gates (rowStart start m ops j) (row start m ops out v j)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [rowsProgram, StraightLine.gates_append, rows_next, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem gates_eq (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) :
    StraightLine.gates (zeroWire start m) (program start m ops out v) =
      [.constant (zeroWire start m) 0] ++
        HessianFamily.gates (zeroWire start m) (copyBase start m) start m ops (m * m) ++
          (List.range m).flatMap (fun j => StraightLine.gates (rowStart start m ops j) (row start m ops out v j)) := by
  rw [program, StraightLine.gates_append, prefix_next, rows_gates_range,
    prefixProgram, StraightLine.gates_append]
  rfl

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
