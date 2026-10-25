/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexHessianCircuit
public import LeanCanny.Computation.PolyTimeArithmetic
public import LeanCanny.Computation.PolyTimeRange

/-! # Native generation of initialized Hessian copies

All selectors, wire offsets, and seed ranges are unary controls. The original
source and integer payloads retain their literal encodings; two derivative
passes and relocation preserve shared intermediate wires.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Hessian
open LeanCanny.Encoding.Brackets

theorem seed_gate_mem_FP {zWire base j k r : List Bool → ℕ}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hj : UnaryFn j) (hk : UnaryFn k) (hr : UnaryFn r) :
    (fun c => ((seedOp (zWire c) (j c) (k c) (r c)).gate (base c + r c)).encode) ∈ FP := by
  have hq := hr.div (UnaryFn.const 4)
  have hi := hr.div (UnaryFn.const 16)
  have h0 := FPPred.eq (hr.mod (UnaryFn.const 4)) (UnaryFn.const 0)
  have h3 := FPPred.eq (hr.mod (UnaryFn.const 4)) (UnaryFn.const 3)
  have h00 := FPPred.eq (hq.mod (UnaryFn.const 4)) (UnaryFn.const 0)
  have h03 := FPPred.eq (hq.mod (UnaryFn.const 4)) (UnaryFn.const 3)
  have hc0 := constantGateBits_mem_FP (hb.add hr) (constFn_mem_FP (Term.const 0).toData.toBits)
  have hc1 := constantGateBits_mem_FP (hb.add hr) (constFn_mem_FP (Term.const 1).toData.toBits)
  have hcj := (FPPred.eq hi hj).ite_mem_FP hc1 hc0
  have hck := (FPPred.eq hi hk).ite_mem_FP hc1 hc0
  have ha := arithmeticGateBits_mem_FP 1 (hb.add hr) hi hz
  have h := h0.ite_mem_FP (h00.ite_mem_FP ha (h03.ite_mem_FP hcj hc0))
    ((h3.and h00).ite_mem_FP hck hc0)
  apply mem_FP_of_eq h
  intro c
  simp only [constantGateBits_encode, addGateBits_encode]
  unfold seedOp
  split_ifs <;> rfl

theorem seeds_forest_mem_FP {zWire base start j k : List Bool → ℕ}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hs : UnaryFn start) (hj : UnaryFn j) (hk : UnaryFn k) :
    (fun c => forest (StraightLine.gates (base c) (seeds (zWire c) (start c) (j c) (k c)))) ∈ FP := by
  have hz' := UnaryFn.comp (f := zWire) (g := pairFst) hz pairFst_mem_FP
  have hb' := UnaryFn.comp (f := base) (g := pairFst) hb pairFst_mem_FP
  have hj' := UnaryFn.comp (f := j) (g := pairFst) hj pairFst_mem_FP
  have hk' := UnaryFn.comp (f := k) (g := pairFst) hk pairFst_mem_FP
  have h := flatMap_range_mem_FP (seed_gate_mem_FP hz' hb' hj' hk' (UnaryFn.length pairSnd_mem_FP))
    (((UnaryFn.const 16).mul hs).mem_FP)
  apply mem_FP_of_eq h
  intro c
  simp only [List.length_replicate, pairFst_pair, pairSnd_pair, seeds_gates,
    forest, List.map_map, List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq]

theorem program_encode_mem_FP {zWire base start j k : List Bool → ℕ} {ops : List Bool → List Operation}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hs : UnaryFn start) (hj : UnaryFn j) (hk : UnaryFn k)
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (base c)
      (program (zWire c) (base c) (start c) (j c) (k c) (ops c)))) ∈ FP := by
  have hbody := WireShift.encode_mem_FP hb (Differential.second_encode_mem_FP hg)
  have h := mem_FP_comp (appendFn_mem_FP (seeds_forest_mem_FP hz hb hs hj hk)
    (mem_FP_comp hbody contents_mem_FP)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode]
  rw [encode_eq_wrap, gates_eq, forest_append]

theorem source_encode_mem_FP {zWire base j k : List Bool → ℕ} {source : List Bool → List Bool}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hj : UnaryFn j) (hk : UnaryFn k) (ht : source ∈ FP) :
    (fun c => encode (StraightLine.gates (base c)
      (program (zWire c) (base c) (TermView.term (source c)).toData.size (j c) (k c)
        (Source.program (TermView.term (source c)).toData.size (TermView.term (source c)))))) ∈ FP := by
  have hs : UnaryFn (fun c => (TermView.term (source c)).toData.size) :=
    (UnaryFn.length (mem_FP_comp ht TermView.normalize_mem_FP)).of_eq
      (fun c => by simp only [Function.comp_apply, TermView.normalize_eq_term, Data.length_toBits])
  apply program_encode_mem_FP hz hb hs hj hk
  simpa only [Source.gates_eq] using Source.encoded_gates_mem_FP ht

end LeanCanny.ETR.ComplexCircuit.Hessian
