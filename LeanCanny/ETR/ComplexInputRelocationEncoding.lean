/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInputRelocation
public import LeanCanny.Computation.PolyTimeArithmetic
public import LeanCanny.Computation.PolyTimeRange

/-! # Native source input relocation

The encoded generator copies a unary-sized input block and shifts the
original gate list, retaining its binary integer payloads and shared wires.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.InputRelocation
open LeanCanny.Encoding.Brackets

theorem seeds_gates (zWire offset base count : ℕ) :
    StraightLine.gates base (seeds zWire offset count) =
      (List.range count).map (fun i => Gate.add (base + i) (offset + i) zWire) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [seeds, List.range_succ, List.map_append, StraightLine.gates_append]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, StraightLine.gates,
      Operation.gate, List.map_append]
    rw [show StraightLine.gates base ((List.range count).map (fun i => Operation.add (offset + i) zWire)) =
      (List.range count).map (fun i => Gate.add (base + i) (offset + i) zWire) from ih]

theorem gates_eq (offset base start : ℕ) (ops : List Operation) :
    StraightLine.gates base (program offset base start ops) =
      Gate.constant base 0 :: (StraightLine.gates (base + 1) (seeds base offset start) ++
        (StraightLine.gates start ops).map (Gate.shift (base + 1))) := by
  rw [program, StraightLine.gates, StraightLine.gates_append, seeds_length, StraightLine.shift_gates]
  rfl

theorem seeds_forest_mem_FP {zWire offset base count : List Bool → ℕ}
    (hz : UnaryFn zWire) (ho : UnaryFn offset) (hb : UnaryFn base) (hc : UnaryFn count) :
    (fun c => forest (StraightLine.gates (base c) (seeds (zWire c) (offset c) (count c)))) ∈ FP := by
  have hi := UnaryFn.length pairSnd_mem_FP
  have h := flatMap_range_mem_FP
    (arithmeticGateBits_mem_FP 1 ((hb.comp pairFst_mem_FP).add hi)
      ((ho.comp pairFst_mem_FP).add hi) (hz.comp pairFst_mem_FP)) hc.mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [seeds_gates, forest, List.map_map, List.flatten_eq_flatMap, List.flatMap_map,
    Function.comp_def, pairFst_pair, pairSnd_pair, List.length_replicate, addGateBits_encode, id_eq]

theorem program_encode_mem_FP {offset base start : List Bool → ℕ} {ops : List Bool → List Operation}
    (ho : UnaryFn offset) (hb : UnaryFn base) (hs : UnaryFn start)
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (base c) (program (offset c) (base c) (start c) (ops c)))) ∈ FP := by
  have hnext := hb.add (UnaryFn.const 1)
  have hbody := WireShift.encode_mem_FP hnext hg
  have hseed := seeds_forest_mem_FP hb ho hnext hs
  have hzero := constantGateBits_mem_FP hb (constFn_mem_FP (Term.const 0).toData.toBits)
  have h := mem_FP_comp (appendFn_mem_FP hzero (appendFn_mem_FP hseed (mem_FP_comp hbody contents_mem_FP))) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp [forest, List.map_append, List.flatten_append]

end LeanCanny.ETR.ComplexCircuit.InputRelocation
