/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelEncoding

/-! # Native PSPACE tests for normalized source critical kernels

Source syntax is compiled and differentiated by the actual shared-network
writers. The native cost certificates hold on every input word. Correctness
for the intended normalized kernel predicate requires an in-range chart.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open MvPolynomial LeanCanny.Computation
open scoped Classical

theorem source_satisfiable (start m : ℕ) (t : Term) (ht : t.arity ≤ start) (v : ℕ → ℤ)
    (chart : ℕ) (hi : chart < m) :
    Satisfiable (query start m (Source.program start t) (Source.output start t) v chart) ↔
      Bad t.toPolynomial m v chart := by
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (Source.program start t)
  have hw := Source.wellFormed start t ht
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start (Source.program start t) hw
  have hin : ∀ i < start, wire i = X i := fun i h => Differential.symbolicRun_preserves_before _ _ _ i h
  have ho : Source.output start t < start + (Source.program start t).length := by
    simpa only [Source.program_length] using Source.output_lt start t ht
  have h := query_satisfiable wire start m (Source.program start t) (Source.output start t) v chart hi hw hr hin ho
  simpa only [wire, Source.symbolicRun_output start t ht] using h

noncomputable def sourceQuery (source : List Bool → List Bool) (m chart : List Bool → ℕ)
    (v : List Bool → ℕ → ℤ) (c : List Bool) : List Gate :=
  query (TermView.term (source c)).toData.size (m c)
    (Source.program (TermView.term (source c)).toData.size (TermView.term (source c)))
    (Source.output (TermView.term (source c)).toData.size (TermView.term (source c))) (v c) (chart c)

theorem sourceQuery_encode_mem_FP {source : List Bool → List Bool} {m chart : List Bool → ℕ}
    {v : List Bool → ℕ → ℤ} (ht : source ∈ FP) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (sourceQuery source m chart v c)) ∈ FP := by
  have hs : UnaryFn (fun c => (TermView.term (source c)).toData.size) :=
    (UnaryFn.length (mem_FP_comp ht TermView.normalize_mem_FP)).of_eq
      (fun c => by simp only [Function.comp_apply, TermView.normalize_eq_term, Data.length_toBits])
  have ho : UnaryFn (fun c => Source.output (TermView.term (source c)).toData.size (TermView.term (source c))) :=
    (UnaryFn.comp (f := Source.Machine.outputIndex) (g := source) Source.Machine.outputIndex_unary ht).of_eq
      (fun c => Source.Machine.outputIndex_eq (source c))
  have hn := UnaryFn.comp (f := Source.Machine.nextIndex) (g := source) Source.Machine.nextIndex_unary ht
  have hlen : UnaryFn (fun c => (Source.program (TermView.term (source c)).toData.size (TermView.term (source c))).length) :=
    (hn.sub hs).of_eq (fun c => by
      simp only [Source.Machine.nextIndex_eq, Nat.add_sub_cancel_left, Source.program_length])
  have hg : (fun c => encode (StraightLine.gates (TermView.term (source c)).toData.size
      (Source.program (TermView.term (source c)).toData.size (TermView.term (source c))))) ∈ FP := by
    simpa only [Source.gates_eq] using Source.encoded_gates_mem_FP ht
  exact query_encode_mem_FP hs hm ho hi hlen hg hv

noncomputable def sourceBad (source : List Bool → List Bool) (m chart : List Bool → ℕ)
    (v : List Bool → ℕ → ℤ) (c : List Bool) : List Bool := [decide (Satisfiable (sourceQuery source m chart v c))]
noncomputable def sourceEmpty (source : List Bool → List Bool) (m chart : List Bool → ℕ)
    (v : List Bool → ℕ → ℤ) (c : List Bool) : List Bool := [decide (¬ Satisfiable (sourceQuery source m chart v c))]

theorem sourceBad_evaluator {source : List Bool → List Bool} {m chart : List Bool → ℕ}
    {v : List Bool → ℕ → ℤ} (ht : source ∈ FP) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    SpaceFunction (sourceBad source m chart v) := feasible_generated (sourceQuery_encode_mem_FP ht hm hi hv)

theorem sourceEmpty_evaluator {source : List Bool → List Bool} {m chart : List Bool → ℕ}
    {v : List Bool → ℕ → ℤ} (ht : source ∈ FP) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    SpaceFunction (sourceEmpty source m chart v) := empty_generated (sourceQuery_encode_mem_FP ht hm hi hv)

theorem sourceBad_correct (source : List Bool → List Bool) (m chart : List Bool → ℕ)
    (v : List Bool → ℕ → ℤ) (c : List Bool) (hi : chart c < m c) :
    sourceBad source m chart v c = [decide (Bad (TermView.term (source c)).toPolynomial (m c) (v c) (chart c))] := by
  simp only [sourceBad, sourceQuery, source_satisfiable _ _ _ (Term.arity_le_dataSize _) _ _ hi]

theorem sourceEmpty_correct (source : List Bool → List Bool) (m chart : List Bool → ℕ)
    (v : List Bool → ℕ → ℤ) (c : List Bool) (hi : chart c < m c) :
    sourceEmpty source m chart v c = [decide (¬ Bad (TermView.term (source c)).toPolynomial (m c) (v c) (chart c))] := by
  simp only [sourceEmpty, sourceQuery, source_satisfiable _ _ _ (Term.arity_le_dataSize _) _ _ hi]

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
