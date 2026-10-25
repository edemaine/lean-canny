/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSampledEncoding
public import LeanCanny.ETR.ComplexCriticalKernelPSPACE

/-! # Native critical-kernel tests for the computed sampled source

The original term, frozen sample, leading coefficient, pure-power exponent,
and dyadic exponent all feed the actual source circuit before differentiation.
Cost certificates are unconditional; source-layout conditions appear only in
the semantic equivalence with the constructed source polynomial.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SampledSource
open MvPolynomial LeanCanny.Computation
open scoped Classical

theorem kernel_satisfiable (oldStart start m : ℕ) (sample a : ℤ) (t : Term) (bits exponent : List Bool)
    (v : ℕ → ℤ) (chart : ℕ) (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hm : m ≤ start) (hi : chart < m) :
    Satisfiable (CriticalKernel.query start m (program oldStart start m sample a t bits exponent)
      (output start m t bits exponent) v chart) ↔
        CriticalKernel.Bad (polynomial m sample a t bits exponent) m v chart := by
  let ops := program oldStart start m sample a t bits exponent
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops
  have hw := wellFormed oldStart start m sample a t bits exponent ht hs hm
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start ops hw
  have hin : ∀ i < start, wire i = X i := fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi
  have h := CriticalKernel.query_satisfiable wire start m ops (output start m t bits exponent) v chart hi hw hr hin
    (output_lt oldStart start m sample a t bits exponent)
  simpa only [wire, ops, symbolic_output oldStart start m sample a t bits exponent ht hs hm] using h

noncomputable def kernelQuery (source bits exponent : List Bool → List Bool) (start m chart : List Bool → ℕ)
    (sample a : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool) : List Gate :=
  CriticalKernel.query (start c) (m c)
    (program (TermView.term (source c)).toData.size (start c) (m c) (sample c) (a c)
      (TermView.term (source c)) (bits c) (exponent c))
    (output (start c) (m c) (TermView.term (source c)) (bits c) (exponent c)) (v c) (chart c)

theorem kernelQuery_encode_mem_FP {source bits exponent : List Bool → List Bool} {start m chart : List Bool → ℕ}
    {sample a : List Bool → ℤ} {v : List Bool → ℕ → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) (he : bits ∈ FP) (hE : exponent ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (kernelQuery source bits exponent start m chart sample a v c)) ∈ FP :=
  CriticalKernel.query_encode_mem_FP hs hm (output_unary ht hs hm he hE) hi (length_unary ht hm he hE)
    (encode_mem_FP ht hs hm hsample ha he hE) hv

noncomputable def kernelBad (source bits exponent : List Bool → List Bool) (start m chart : List Bool → ℕ)
    (sample a : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  [decide (Satisfiable (kernelQuery source bits exponent start m chart sample a v c))]

noncomputable def kernelEmpty (source bits exponent : List Bool → List Bool) (start m chart : List Bool → ℕ)
    (sample a : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  [decide (¬ Satisfiable (kernelQuery source bits exponent start m chart sample a v c))]

theorem kernelBad_evaluator {source bits exponent : List Bool → List Bool} {start m chart : List Bool → ℕ}
    {sample a : List Bool → ℤ} {v : List Bool → ℕ → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) (he : bits ∈ FP) (hE : exponent ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    SpaceFunction (kernelBad source bits exponent start m chart sample a v) :=
  feasible_generated (kernelQuery_encode_mem_FP ht hs hm hi hsample ha he hE hv)

theorem kernelEmpty_evaluator {source bits exponent : List Bool → List Bool} {start m chart : List Bool → ℕ}
    {sample a : List Bool → ℤ} {v : List Bool → ℕ → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) (he : bits ∈ FP) (hE : exponent ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    SpaceFunction (kernelEmpty source bits exponent start m chart sample a v) :=
  empty_generated (kernelQuery_encode_mem_FP ht hs hm hi hsample ha he hE hv)

theorem kernelBad_correct (source bits exponent : List Bool → List Bool) (start m chart : List Bool → ℕ)
    (sample a : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool)
    (hs : (TermView.term (source c)).toData.size ≤ start c) (hm : m c ≤ start c) (hi : chart c < m c) :
    kernelBad source bits exponent start m chart sample a v c =
      [decide (CriticalKernel.Bad (polynomial (m c) (sample c) (a c) (TermView.term (source c)) (bits c) (exponent c))
        (m c) (v c) (chart c))] := by
  simp only [kernelBad, kernelQuery, kernel_satisfiable _ _ _ _ _ _ _ _ _ _ (Term.arity_le_dataSize _) hs hm hi]

end LeanCanny.ETR.ComplexCircuit.SampledSource
