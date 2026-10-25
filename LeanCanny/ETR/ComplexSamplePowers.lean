/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenSource
public import LeanCanny.ETR.ComplexInfinityEncoding
public import LeanCanny.ETR.ComplexDifferentialSymbolic

/-! # Shared pure-power sums at a frozen sweep coordinate

The first input of the existing power-sum program is redirected to the computed
sample wire; the remaining inputs are the spatial coordinates. All outputs are
relocated after the previous source computation. Binary exponents stay shared.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SamplePowers
open MvPolynomial
open scoped Classical BigOperators

def index (m sampleWire start i : ℕ) : ℕ :=
  if i < m + 1 then (if i = 0 then sampleWire else i - 1) else start + (i - (m + 1))

theorem index_aux (m sampleWire start q : ℕ) : index m sampleWire start (m + 1 + q) = start + q := by
  simp only [index, ite_eq_right (show ¬ m + 1 + q < m + 1 by omega), Nat.add_sub_cancel_left]

theorem index_input_zero (m sampleWire start : ℕ) : index m sampleWire start 0 = sampleWire := by
  simp only [index, Nat.zero_lt_succ, ite_true]

theorem index_input_succ (m sampleWire start i : ℕ) (hi : i < m) : index m sampleWire start (i + 1) = i := by
  simp only [index, ite_eq_left (show i + 1 < m + 1 by omega), Nat.add_one_ne_zero, ite_false,
    Nat.add_sub_cancel_right]

def program (m sampleWire start : ℕ) (bits : List Bool) : List Operation :=
  (Infinity.prefixProgram (m + 1) bits (fun _ => 0) (m + 1)).map (Operation.reindex (index m sampleWire start))
def output (m sampleWire start : ℕ) (bits : List Bool) : ℕ :=
  index m sampleWire start (Infinity.sumWire (m + 1) bits (m + 1))

theorem program_length (m sampleWire start : ℕ) (bits : List Bool) :
    (program m sampleWire start bits).length = 1 + (m + 1) * Infinity.stride bits := by
  simp only [program, List.length_map, Infinity.prefix_length]

theorem wellFormed (m sampleWire start : ℕ) (bits : List Bool) (hs : sampleWire < start) (hm : m ≤ start) :
    StraightLine.WellFormed start (program m sampleWire start bits) := by
  apply StraightLine.reindex_wellFormed _ (m + 1) start _ (Infinity.wellFormed _ bits _ _ le_rfl)
  intro q i hi
  unfold index
  split_ifs <;> omega

theorem gates_eq (m sampleWire start : ℕ) (bits : List Bool) :
    StraightLine.gates start (program m sampleWire start bits) =
      (Infinity.prefixGates (m + 1) bits (fun _ => 0) (m + 1)).map (Gate.reindex (index m sampleWire start)) :=
  StraightLine.reindex_gates _ (m + 1) start _ (index_aux m sampleWire start)

theorem output_lt (m sampleWire start : ℕ) (bits : List Bool) :
    output m sampleWire start bits < start + (program m sampleWire start bits).length := by
  have hs : m + 1 ≤ Infinity.sumWire (m + 1) bits (m + 1) := by
    simp only [Infinity.sumWire, Infinity.powerWire, Infinity.start]
    omega
  have ht := Infinity.sumWire_lt_start (m + 1) bits (m + 1)
  unfold output index
  rw [ite_eq_right (by omega), program_length]
  unfold Infinity.start at ht
  omega

theorem sound (m sampleWire start : ℕ) (bits : List Bool) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates start (program m sampleWire start bits), g.Holds env) :
    env (output m sampleWire start bits) = env sampleWire ^ (Nat.fromBitsLE bits + 1) +
      ∑ i ∈ Finset.range m, env i ^ (Nat.fromBitsLE bits + 1) := by
  have hb : ∀ g ∈ Infinity.prefixGates (m + 1) bits (fun _ => 0) (m + 1),
      g.Holds (fun i => env (index m sampleWire start i)) := by
    intro g h
    apply (Gate.reindex_holds _ g env).mp
    exact hg _ (by rw [gates_eq]; exact List.mem_map.mpr ⟨g, h, rfl⟩)
  have h := Infinity.sum_sound (m + 1) bits (fun _ => 0) (m + 1) _ hb
  change env (output m sampleWire start bits) = _ at h
  rw [Finset.sum_range_succ', index_input_zero] at h
  refine h.trans ((add_comm _ _).trans (congrArg₂ (· + ·) rfl ?_))
  apply Finset.sum_congr rfl
  intro i hi
  rw [index_input_succ m sampleWire start i (Finset.mem_range.mp hi)]

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (m sampleWire start : ℕ) (bits : List Bool)
    (hr : Differential.Realizes wire start (program m sampleWire start bits)) :
    wire (output m sampleWire start bits) = wire sampleWire ^ (Nat.fromBitsLE bits + 1) +
      ∑ i ∈ Finset.range m, wire i ^ (Nat.fromBitsLE bits + 1) := by
  apply Differential.eq_of_eval_complex
  intro x
  have h := sound m sampleWire start bits (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x)
    (Differential.realizes_gates_eval wire start _ hr x)
  simpa only [eval₂_add, eval₂_pow, eval₂_sum] using h

end LeanCanny.ETR.ComplexCircuit.SamplePowers
