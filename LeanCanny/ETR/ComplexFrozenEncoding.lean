/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenSource

/-! # Native generation of frozen source circuits

The index scanner captures both original and new input bounds. It retains the
original binary constants and adds one binary sample literal. Source size,
output, and operation count are obtained from the validated source compiler.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.FrozenSource
open LeanCanny.Encoding.Brackets

theorem index_unary {oldStart start i : List Bool → ℕ}
    (ho : UnaryFn oldStart) (hs : UnaryFn start) (hi : UnaryFn i) :
    UnaryFn (fun c => index (oldStart c) (start c) (i c)) :=
  (UnaryFn.ite (FPPred.lt hi ho) (UnaryFn.ite (FPPred.eq hi (UnaryFn.const 0)) hs (hi.sub (UnaryFn.const 1)))
    ((hs.add (UnaryFn.const 1)).add (hi.sub ho))).of_eq (fun _ => rfl)

namespace Encoded

def index (par : List Bool) (i : ℕ) : ℕ := FrozenSource.index (pairFst par).length (pairSnd par).length i

theorem index_pair (oldStart start : ℕ) :
    index (pair (List.replicate oldStart true) (List.replicate start true)) = FrozenSource.index oldStart start := by
  funext i
  simp only [index, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem index_unary : UnaryFn (fun p => index (pairFst p) (pairSnd p).length) :=
  FrozenSource.index_unary
    (UnaryFn.length (mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP))
    (UnaryFn.length (mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP))
    (UnaryFn.length pairSnd_mem_FP)

end Encoded

theorem source_start_unary {source : List Bool → List Bool} (ht : source ∈ FP) :
    UnaryFn (fun c => (TermView.term (source c)).toData.size) :=
  (UnaryFn.length (mem_FP_comp ht TermView.normalize_mem_FP)).of_eq
    (fun c => by simp only [Function.comp_apply, TermView.normalize_eq_term, Data.length_toBits])

theorem encode_mem_FP {source : List Bool → List Bool} {start : List Bool → ℕ} {sample : List Bool → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start)
    (hliteral : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (TermView.term (source c)).toData.size (start c) (sample c) (TermView.term (source c))))) ∈ FP := by
  have hpar := mem_FP_pair (source_start_unary ht).mem_FP hs.mem_FP
  have hbody := Reindex.encode_mem_FP Encoded.index_unary hpar (Source.encoded_gates_mem_FP ht)
  have h := mem_FP_comp (appendFn_mem_FP (constantGateBits_mem_FP hs hliteral)
    (mem_FP_comp hbody contents_mem_FP)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, constantGateBits_encode, contents_encode]
  rw [encode_eq_wrap, gates_eq, forest_cons]
  rw [Encoded.index_pair]

theorem output_unary {source : List Bool → List Bool} {start : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) :
    UnaryFn (fun c => output (TermView.term (source c)).toData.size (start c) (TermView.term (source c))) := by
  have ho := UnaryFn.comp (f := Source.Machine.outputIndex) (g := source) Source.Machine.outputIndex_unary ht
  exact (index_unary (source_start_unary ht) hs ho).of_eq
    (fun c => by simp only [Source.Machine.outputIndex_eq, output])

theorem length_unary {source : List Bool → List Bool} {start : List Bool → ℕ} {sample : List Bool → ℤ}
    (ht : source ∈ FP) :
    UnaryFn (fun c => (program (TermView.term (source c)).toData.size (start c) (sample c) (TermView.term (source c))).length) := by
  have hn := UnaryFn.comp (f := Source.Machine.nextIndex) (g := source) Source.Machine.nextIndex_unary ht
  exact (((hn.sub (source_start_unary ht)).add (UnaryFn.const 1))).of_eq
    (fun c => by simp only [Source.Machine.nextIndex_eq, Nat.add_sub_cancel_left, program_length])

end LeanCanny.ETR.ComplexCircuit.FrozenSource
