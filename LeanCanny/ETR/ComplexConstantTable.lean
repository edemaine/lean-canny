/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitCompiler
public import LeanCanny.ETR.ComplexCircuitBuilders
public import LeanCanny.ETR.ComplexInputRelocation
public import LeanCanny.Computation.PolyTimeRange

/-! # Shared tables of binary integer constants

One acyclic operation per table entry captures normal coefficients for later
affine rows. Uniform literal access charges their binary payloads explicitly.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.ConstantTable
open LeanCanny.Encoding.Brackets MvPolynomial
open scoped Classical

def program (count : ℕ) (value : ℕ → ℤ) : List Operation :=
  (List.range count).map (fun i => .constant (value i))

theorem program_length (count : ℕ) (value : ℕ → ℤ) : (program count value).length = count := by
  simp only [program, List.length_map, List.length_range]

theorem gates_eq (base count : ℕ) (value : ℕ → ℤ) :
    StraightLine.gates base (program count value) = (List.range count).map (fun i => Gate.constant (base + i) (value i)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [program, List.range_succ, List.map_append, StraightLine.gates_append]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, StraightLine.gates, Operation.gate, List.map_append]
    rw [show StraightLine.gates base ((List.range count).map (fun i => Operation.constant (value i))) =
      (List.range count).map (fun i => Gate.constant (base + i) (value i)) from ih]

theorem wellFormed (base count : ℕ) (value : ℕ → ℤ) : StraightLine.WellFormed base (program count value) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [program, List.range_succ, List.map_append, StraightLine.wellFormed_append]
    exact ⟨ih, trivial, trivial⟩

theorem sound (base count : ℕ) (value : ℕ → ℤ) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates base (program count value), g.Holds env) (i : ℕ) (hi : i < count) :
    env (base + i) = (value i : ℂ) := by
  apply hg (.constant (base + i) (value i))
  rw [gates_eq]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem symbolic {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (base count : ℕ) (value : ℕ → ℤ)
    (i : ℕ) (hi : i < count) : Differential.symbolicRun wire base (program count value) (base + i) = C (value i) := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [program, List.range_succ, List.map_append, Differential.symbolicRun_append]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, Differential.symbolicRun]
    by_cases he : i = count
    · subst i
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (show base + i ≠ base + count by omega)]
      exact ih (by omega)

theorem encode_FP {base count : List Bool → ℕ} {value : List Bool → ℕ → ℤ}
    (hb : UnaryFn base) (hn : UnaryFn count)
    (hv : (fun q => (Term.const (value (pairFst q) (pairSnd q).length)).toData.toBits) ∈ FP) :
    (fun c => encode (StraightLine.gates (base c) (program (count c) (value c)))) ∈ FP := by
  have hgate := constantGateBits_mem_FP ((hb.comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP)) hv
  have H := flatMap_range_mem_FP hgate hn.mem_FP
  apply mem_FP_of_eq (mem_FP_comp H wrap_mem_FP)
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest, List.map_map, List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq]

end LeanCanny.ETR.ComplexCircuit.ConstantTable
