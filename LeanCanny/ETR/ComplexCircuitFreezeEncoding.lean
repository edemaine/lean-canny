/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitFreeze

/-! # Native generation of shared circuits with a parameter wire

The scanner reindexes the original encoded gate list. All addresses retain
unary certificates, original constants are copied, and the operation count
is unchanged. No literal encoding of the parameter's value is required.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CircuitFreeze
open LeanCanny.Encoding.Brackets

theorem index_unary {inputs parameter start i : List Bool → ℕ}
    (hn : UnaryFn inputs) (hp : UnaryFn parameter) (hs : UnaryFn start) (hi : UnaryFn i) :
    UnaryFn (fun c => index (inputs c) (parameter c) (start c) (i c)) :=
  (UnaryFn.ite (FPPred.lt hi hn) (UnaryFn.ite (FPPred.eq hi (UnaryFn.const 0)) hp (hi.sub (UnaryFn.const 1)))
    (hs.add (hi.sub hn))).of_eq (fun _ => rfl)

namespace Encoded

def index (par : List Bool) (i : ℕ) : ℕ :=
  CircuitFreeze.index (pairFst par).length (pairFst (pairSnd par)).length (pairSnd (pairSnd par)).length i

theorem index_pair (inputs parameter start : ℕ) :
    index (pair (List.replicate inputs true) (pair (List.replicate parameter true) (List.replicate start true))) =
      CircuitFreeze.index inputs parameter start := by
  funext i
  simp only [index, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem index_unary : UnaryFn (fun p => index (pairFst p) (pairSnd p).length) := by
  have hn := mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP
  have ht := mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP
  have hp := mem_FP_comp ht pairFst_mem_FP
  have hs := mem_FP_comp ht pairSnd_mem_FP
  exact CircuitFreeze.index_unary (UnaryFn.length hn) (UnaryFn.length hp) (UnaryFn.length hs) (UnaryFn.length pairSnd_mem_FP)

end Encoded

theorem encode_mem_FP {inputs parameter start : List Bool → ℕ} {ops : List Bool → List Operation}
    (hn : UnaryFn inputs) (hp : UnaryFn parameter) (hs : UnaryFn start)
    (hg : (fun c => encode (StraightLine.gates (inputs c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (start c) (program (inputs c) (parameter c) (start c) (ops c)))) ∈ FP := by
  have hpar := mem_FP_pair hn.mem_FP (mem_FP_pair hp.mem_FP hs.mem_FP)
  have h := Reindex.encode_mem_FP Encoded.index_unary hpar hg
  apply mem_FP_of_eq h
  intro c
  rw [gates_eq, Encoded.index_pair]

theorem output_unary {inputs parameter start out : List Bool → ℕ}
    (hn : UnaryFn inputs) (hp : UnaryFn parameter) (hs : UnaryFn start) (ho : UnaryFn out) :
    UnaryFn (fun c => output (inputs c) (parameter c) (start c) (out c)) := index_unary hn hp hs ho

theorem length_unary {inputs parameter start : List Bool → ℕ} {ops : List Bool → List Operation}
    (hl : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => (program (inputs c) (parameter c) (start c) (ops c)).length) :=
  hl.of_eq (fun c => (program_length (inputs c) (parameter c) (start c) (ops c)).symm)

end LeanCanny.ETR.ComplexCircuit.CircuitFreeze
