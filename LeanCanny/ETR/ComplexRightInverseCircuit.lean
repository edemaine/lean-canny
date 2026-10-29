/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexKernelRowEncoding
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Shared right-inverse guards

A polynomial number of shared arithmetic rows checks a square matrix times
a matrix of auxiliary input variables against the identity. Such guards can
restrict parent assignments to regular roots while child variables remain
complex and unrestricted.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RightInverse
open scoped Classical BigOperators

def coefficient (i j : ℕ) : ℤ := if i = j then -1 else 0

def row (zWire one base inverse n i j : ℕ) (entry : ℕ → ℕ → ℕ) : List Operation :=
  KernelRow.program zWire base (inverse + j * n) n (KernelRow.sumWire zWire base n) one
    (coefficient i j) (fun _ => zWire) (entry i)

def stride (n : ℕ) : ℕ := 4 * n + 3
def rowStart (base n q : ℕ) : ℕ := base + q * stride n

def program (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) : ℕ → List Operation
  | 0 => []
  | q + 1 => program zWire one base inverse n entry q ++
      row zWire one (rowStart base n q) inverse n (q / n) (q % n) entry

def gates (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (count : ℕ) : List Gate :=
  StraightLine.gates base (program zWire one base inverse n entry count)

def output (base n q : ℕ) : ℕ := KernelRow.criticalWire (rowStart base n q) n

theorem row_length (zWire one base inverse n i j : ℕ) (entry : ℕ → ℕ → ℕ) :
    (row zWire one base inverse n i j entry).length = stride n :=
  KernelRow.program_length ..

theorem program_length (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (count : ℕ) :
    (program zWire one base inverse n entry count).length = count * stride n := by
  induction count with
  | zero => simp only [program, List.length_nil, Nat.zero_mul]
  | succ count ih => rw [program, List.length_append, row_length, ih, Nat.succ_mul]

theorem gates_succ (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (count : ℕ) :
    gates zWire one base inverse n entry (count + 1) = gates zWire one base inverse n entry count ++
      StraightLine.gates (rowStart base n count) (row zWire one (rowStart base n count) inverse n (count / n) (count % n) entry) := by
  rw [gates, program, StraightLine.gates_append, program_length]
  rfl

theorem gates_range (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (count : ℕ) :
    gates zWire one base inverse n entry count = (List.range count).flatMap (fun q =>
      StraightLine.gates (rowStart base n q) (row zWire one (rowStart base n q) inverse n (q / n) (q % n) entry)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [gates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem output_lt (base n count q : ℕ) (hq : q < count) :
    output base n q < base + count * stride n := by
  have hm := Nat.mul_le_mul_right (stride n) (show q + 1 ≤ count from hq)
  rw [Nat.add_mul, Nat.one_mul] at hm
  unfold output KernelRow.criticalWire rowStart stride at *
  omega

theorem row_wellFormed (zWire one base inverse n i j : ℕ) (entry : ℕ → ℕ → ℕ)
    (hz : zWire < base) (ho : one < base) (he : ∀ k < n, entry i k < base)
    (hu : inverse + j * n + n ≤ base) :
    StraightLine.WellFormed base (row zWire one base inverse n i j entry) := by
  rw [row, KernelRow.program, StraightLine.wellFormed_append, KernelRow.prefix_length]
  refine ⟨KernelRow.prefix_wellFormed _ _ _ _ _ _ _ hz (fun _ _ => hz) he hu, ?_⟩
  have hs : KernelRow.sumWire zWire base n < base + (1 + 4 * n) := by
    unfold KernelRow.sumWire
    split_ifs <;> omega
  simp only [StraightLine.WellFormed, Operation.InputsBelow]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, trivial⟩

theorem row_sound (zWire one base inverse n i j : ℕ) (entry : ℕ → ℕ → ℕ) (env : ℕ → ℂ)
    (hz : env zWire = 0) (ho : env one = 1)
    (hg : ∀ g ∈ StraightLine.gates base (row zWire one base inverse n i j entry), g.Holds env) :
    env (KernelRow.criticalWire base n) =
      (∑ k ∈ Finset.range n, env (entry i k) * env (inverse + j * n + k)) + (coefficient i j : ℂ) := by
  obtain ⟨hs, hv⟩ := KernelRow.sound zWire base (inverse + j * n) n
    (KernelRow.sumWire zWire base n) one (coefficient i j) (fun _ => zWire) (entry i) env hz hg
  simpa only [hs, hz, ho, mul_zero, add_zero, mul_one] using hv

theorem wellFormed (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ)
    (hz : zWire < base) (ho : one < base) (he : ∀ i < n, ∀ k < n, entry i k < base)
    (hu : inverse + n * n ≤ base) (count : ℕ) (hc : count ≤ n * n) :
    StraightLine.WellFormed base (program zWire one base inverse n entry count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [program, StraightLine.wellFormed_append, program_length]
    refine ⟨ih (by omega), ?_⟩
    have hn : 0 < n := by nlinarith
    have hi : count / n < n := (Nat.div_lt_iff_lt_mul hn).mpr (by omega)
    have hj : count % n < n := Nat.mod_lt _ hn
    have hmul : (count % n + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    have hb : base ≤ rowStart base n count := by unfold rowStart; omega
    apply row_wellFormed _ _ _ _ _ _ _ _ (hz.trans_le hb) (ho.trans_le hb) (fun k hk => (he _ hi k hk).trans_le hb)
    dsimp only [rowStart]
    have hid : count % n * n + n = (count % n + 1) * n := by ring
    omega

theorem sound (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (count : ℕ) (env : ℕ → ℂ)
    (hz : env zWire = 0) (ho : env one = 1)
    (hg : ∀ g ∈ gates zWire one base inverse n entry count, g.Holds env)
    (q : ℕ) (hq : q < count) :
    env (output base n q) =
      (∑ k ∈ Finset.range n, env (entry (q / n) k) * env (inverse + q % n * n + k)) + (coefficient (q / n) (q % n) : ℂ) := by
  apply row_sound zWire one (rowStart base n q) inverse n (q / n) (q % n) entry env hz ho
  intro g h
  apply hg g
  rw [gates_range]
  exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, h⟩

noncomputable def matrix (n : ℕ) (entry : ℕ → ℕ → ℕ) (env : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => env (entry i.val k.val)
noncomputable def inverseMatrix (inverse n : ℕ) (env : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k j => env (inverse + j.val * n + k.val)

theorem constraints_iff (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ) (env : ℕ → ℂ)
    (hz : env zWire = 0) (ho : env one = 1)
    (hg : ∀ g ∈ gates zWire one base inverse n entry (n * n), g.Holds env) :
    (∀ q < n * n, env (output base n q) = 0) ↔ matrix n entry env * inverseMatrix inverse n env = 1 := by
  have hrow (i j : Fin n) :
      env (output base n (i.val * n + j.val)) =
        (matrix n entry env * inverseMatrix inverse n env) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
    have hn : 0 < n := by have H := i.isLt; omega
    have hq : i.val * n + j.val < n * n := by
      have H := Nat.mul_le_mul_right n (show i.val + 1 ≤ n from i.isLt)
      have hid : (i.val + 1) * n = i.val * n + n := by ring
      have HJ := j.isLt
      omega
    rw [sound zWire one base inverse n entry (n * n) env hz ho hg _ hq]
    have hd : (i.val * n + j.val) / n = i.val := by
      rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    have hm : (i.val * n + j.val) % n = j.val := by simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
    rw [hd, hm]
    simp only [Matrix.mul_apply, matrix, inverseMatrix,
      coefficient, Matrix.one_apply, Fin.ext_iff]
    rw [← Fin.sum_univ_eq_sum_range]
    split_ifs <;> norm_num [sub_eq_add_neg]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    apply sub_eq_zero.mp
    rw [← hrow]
    apply h
    have H := Nat.mul_le_mul_right n (show i.val + 1 ≤ n from i.isLt)
    have hid : (i.val + 1) * n = i.val * n + n := by ring
    have HJ := j.isLt
    omega
  · intro h q hq
    have hn : 0 < n := by nlinarith
    let i : Fin n := ⟨q / n, (Nat.div_lt_iff_lt_mul hn).mpr hq⟩
    let j : Fin n := ⟨q % n, Nat.mod_lt _ hn⟩
    have he : i.val * n + j.val = q := by
      dsimp only [i, j]
      simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div q n
    rw [← he, hrow, h, sub_self]

/-- Existence of the guarded auxiliary matrix is exactly nonsingularity. -/
theorem exists_inverse_iff (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (∃ B, M * B = 1) ↔ M.det ≠ 0 := by
  rw [← Matrix.mulVec_surjective_iff_exists_right_inverse, Matrix.mulVec_surjective_iff_isUnit,
    M.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem exists_completion (zWire one base inverse n : ℕ) (entry : ℕ → ℕ → ℕ)
    (hz : zWire < base) (ho : one < base) (he : ∀ i < n, ∀ k < n, entry i k < base)
    (hu : inverse + n * n ≤ base) (x : ℕ → ℂ) (hxz : x zWire = 0) (hxo : x one = 1) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ gates zWire one base inverse n entry (n * n), g.Holds env) ∧
      ((∀ q < n * n, env (output base n q) = 0) ↔
        matrix n entry env * inverseMatrix inverse n env = 1) := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x base
    (program zWire one base inverse n entry (n * n))
    (wellFormed zWire one base inverse n entry hz ho he hu _ le_rfl)
  exact ⟨env, hp, hg, constraints_iff zWire one base inverse n entry env
    ((hp _ hz).trans hxz) ((hp _ ho).trans hxo) hg⟩

/-- Complex inverse witnesses select exactly the regular real parent matrices. -/
theorem exists_inverse_real_iff (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, M.map Complex.ofRealHom * B = 1) ↔ M.det ≠ 0 := by
  rw [exists_inverse_iff]
  have hmap : (M.map Complex.ofRealHom).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
  rw [hmap]
  exact not_congr Complex.ofReal_eq_zero

end LeanCanny.ETR.ComplexCircuit.RightInverse
