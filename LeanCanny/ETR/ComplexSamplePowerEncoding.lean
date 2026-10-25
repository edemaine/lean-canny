/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSamplePowers

/-! # Native generation of the sampled pure-power source block -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SamplePowers
open LeanCanny.Encoding.Brackets

theorem index_unary {m sampleWire start i : List Bool → ℕ}
    (hm : UnaryFn m) (hs : UnaryFn sampleWire) (hb : UnaryFn start) (hi : UnaryFn i) :
    UnaryFn (fun c => index (m c) (sampleWire c) (start c) (i c)) :=
  (UnaryFn.ite (FPPred.lt hi (hm.add (UnaryFn.const 1)))
    (UnaryFn.ite (FPPred.eq hi (UnaryFn.const 0)) hs (hi.sub (UnaryFn.const 1)))
    (hb.add (hi.sub (hm.add (UnaryFn.const 1))))).of_eq (fun _ => rfl)

theorem prefix_encode_mem_FP {m : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (he : bits ∈ FP) :
    (fun c => encode (Infinity.prefixGates (m c) (bits c) (fun _ => 0) (m c))) ∈ FP := by
  have hm' := UnaryFn.comp (f := m) (g := pairFst) hm pairFst_mem_FP
  have he' := mem_FP_comp (f := pairFst) (g := bits) pairFst_mem_FP he
  have hk := UnaryFn.length pairSnd_mem_FP
  have hblock := Infinity.block_forest_mem_FP (v := fun _ _ => 0) hm' hk he'
    (constFn_mem_FP (Term.const 0).toData.toBits)
  have hblocks := flatMap_range_mem_FP hblock hm.mem_FP
  have h := mem_FP_comp (appendFn_mem_FP
    (constantGateBits_mem_FP hm (constFn_mem_FP (Term.const 0).toData.toBits)) hblocks) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair, constantGateBits_encode]
  rw [encode_eq_wrap, Infinity.prefixGates_range]
  simp only [forest_append, forest_cons, forest_nil, List.append_nil, Infinity.forest_flatMap]

namespace Encoded

def index (par : List Bool) (i : ℕ) : ℕ :=
  SamplePowers.index (pairFst par).length (pairFst (pairSnd par)).length (pairSnd (pairSnd par)).length i

theorem index_pair (m sampleWire start : ℕ) :
    index (pair (List.replicate m true) (pair (List.replicate sampleWire true) (List.replicate start true))) =
      SamplePowers.index m sampleWire start := by
  funext i
  simp only [index, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem index_unary : UnaryFn (fun p => index (pairFst p) (pairSnd p).length) := by
  have hm := mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP
  have ht := mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP
  have hs := mem_FP_comp ht pairFst_mem_FP
  have hb := mem_FP_comp ht pairSnd_mem_FP
  exact SamplePowers.index_unary (UnaryFn.length hm) (UnaryFn.length hs) (UnaryFn.length hb)
    (UnaryFn.length pairSnd_mem_FP)

end Encoded

theorem encode_mem_FP {m sampleWire start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (hs : UnaryFn sampleWire) (hb : UnaryFn start) (he : bits ∈ FP) :
    (fun c => encode (StraightLine.gates (start c) (program (m c) (sampleWire c) (start c) (bits c)))) ∈ FP := by
  have hpar := mem_FP_pair hm.mem_FP (mem_FP_pair hs.mem_FP hb.mem_FP)
  have h := Reindex.encode_mem_FP Encoded.index_unary hpar (prefix_encode_mem_FP (hm.add (UnaryFn.const 1)) he)
  apply mem_FP_of_eq h
  intro c
  rw [gates_eq, Encoded.index_pair]

theorem output_unary {m sampleWire start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (hs : UnaryFn sampleWire) (hb : UnaryFn start) (he : bits ∈ FP) :
    UnaryFn (fun c => output (m c) (sampleWire c) (start c) (bits c)) :=
  index_unary hm hs hb (Infinity.sumWire_unary (hm.add (UnaryFn.const 1)) (hm.add (UnaryFn.const 1)) he)

theorem length_unary {m sampleWire start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (he : bits ∈ FP) :
    UnaryFn (fun c => (program (m c) (sampleWire c) (start c) (bits c)).length) :=
  ((UnaryFn.const 1).add ((hm.add (UnaryFn.const 1)).mul
    (((UnaryFn.const 2).mul (UnaryFn.length he)).add (UnaryFn.const 6)))).of_eq
      (fun c => (program_length (m c) (sampleWire c) (start c) (bits c)).symm)

end LeanCanny.ETR.ComplexCircuit.SamplePowers
