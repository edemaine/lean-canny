/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRightInverseCircuit
public import LeanCanny.ETR.ComplexCircuitCompiler

/-! # Native polynomial-time right-inverse guard generation -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RightInverse
open LeanCanny.Encoding.Brackets

private theorem entry_comp {entry : List Bool → ℕ → ℕ → ℕ} {f : List Bool → List Bool}
    (he : UnaryFn (fun q => entry (pairFst (pairFst q)) (pairSnd (pairFst q)).length (pairSnd q).length))
    (hf : f ∈ FP) :
    UnaryFn (fun q => entry (f (pairFst (pairFst q))) (pairSnd (pairFst q)).length (pairSnd q).length) := by
  have hp := mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
  exact (he.comp hp).of_eq (fun _ => by simp only [pairFst_pair, pairSnd_pair, Function.comp_apply])

theorem row_encode_mem_FP {zWire one base inverse n i j : List Bool → ℕ}
    {entry : List Bool → ℕ → ℕ → ℕ}
    (hz : UnaryFn zWire) (ho : UnaryFn one) (hb : UnaryFn base) (hu : UnaryFn inverse)
    (hn : UnaryFn n) (hi : UnaryFn i) (hj : UnaryFn j)
    (he : UnaryFn (fun q => entry (pairFst (pairFst q)) (pairSnd (pairFst q)).length (pairSnd q).length)) :
    (fun c => encode (StraightLine.gates (base c)
      (row (zWire c) (one c) (base c) (inverse c) (n c) (i c) (j c) (entry c)))) ∈ FP := by
  have hp := mem_FP_pair (mem_FP_pair pairFst_mem_FP (hi.comp pairFst_mem_FP).mem_FP) pairSnd_mem_FP
  have hentry : UnaryFn (fun q => entry (pairFst q) (i (pairFst q)) (pairSnd q).length) := (he.comp hp).of_eq (fun _ => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate])
  have hc : (fun c => (Term.const (coefficient (i c) (j c))).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq ((FPPred.eq hi hj).ite_mem_FP
      (constFn_mem_FP (Term.const (-1)).toData.toBits) (constFn_mem_FP (Term.const 0).toData.toBits))
    intro c
    by_cases h : i c = j c <;> simp [coefficient, h]
  exact KernelRow.encode_mem_FP (coefficient := fun c => coefficient (i c) (j c))
    (first := fun c _ => zWire c) (entry := fun c => entry c (i c)) hz hb (hu.add (hj.mul hn)) hn (KernelRow.sumWire_unary hz hb hn) ho hc
    (hz.comp pairFst_mem_FP) hentry

theorem program_encode_mem_FP {zWire one base inverse n count : List Bool → ℕ}
    {entry : List Bool → ℕ → ℕ → ℕ}
    (hz : UnaryFn zWire) (ho : UnaryFn one) (hb : UnaryFn base) (hu : UnaryFn inverse)
    (hn : UnaryFn n) (hc : UnaryFn count)
    (he : UnaryFn (fun q => entry (pairFst (pairFst q)) (pairSnd (pairFst q)).length (pairSnd q).length)) :
    (fun c => encode (gates (zWire c) (one c) (base c) (inverse c) (n c) (entry c) (count c))) ∈ FP := by
  have hq := UnaryFn.length pairSnd_mem_FP
  have hn' := hn.comp pairFst_mem_FP
  have hbase := (hb.comp pairFst_mem_FP).add (hq.mul (((UnaryFn.const 4).mul hn').add (UnaryFn.const 3)))
  have hrow := row_encode_mem_FP (entry := fun c i k => entry (pairFst c) i k) (hz.comp pairFst_mem_FP) (ho.comp pairFst_mem_FP) hbase
    (hu.comp pairFst_mem_FP) hn' (hq.div hn') (hq.mod hn') (entry_comp he pairFst_mem_FP)
  have H := flatMap_range_mem_FP (mem_FP_comp hrow contents_mem_FP) hc.mem_FP
  apply mem_FP_of_eq (mem_FP_comp H wrap_mem_FP)
  intro c
  simp only [Function.comp_apply, contents_encode, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [encode_eq_wrap, gates_range]
  simp only [forest, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_assoc]
  rfl

theorem output_unary {base n q : List Bool → ℕ} (hb : UnaryFn base) (hn : UnaryFn n) (hq : UnaryFn q) :
    UnaryFn (fun c => output (base c) (n c) (q c)) :=
  (((hb.add (hq.mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3)))).add
    ((UnaryFn.const 4).mul hn)).add (UnaryFn.const 2)).of_eq (fun _ => rfl)

theorem length_unary {zWire one base inverse n count : List Bool → ℕ}
    (hn : UnaryFn n) (hc : UnaryFn count) (entry : List Bool → ℕ → ℕ → ℕ) :
    UnaryFn (fun c => (program (zWire c) (one c) (base c) (inverse c) (n c) (entry c) (count c)).length) :=
  (hc.mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3))).of_eq
    (fun _ => (program_length ..).symm)

end LeanCanny.ETR.ComplexCircuit.RightInverse
