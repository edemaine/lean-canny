/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedEncoding
public import LeanCanny.ETR.ComplexCriticalKernelPSPACE

/-! # Native critical-kernel tests for the bounded regular source

The query writer differentiates the actual shared source. Its native space
certificate retains all five binary exponent readers.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedSource
open MvPolynomial LeanCanny.Computation
open scoped Classical

theorem kernel_satisfiable (oldStart start m : ℕ) (sample : ℤ) (t : Term)
    (radius scale shift bits exponent : List Bool) (v : ℕ → ℤ) (chart : ℕ)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hm : m + 2 ≤ start) (hi : chart < m + 2) :
    Satisfiable (CriticalKernel.query start (m + 2)
      (program oldStart start m sample t radius scale shift bits exponent)
      (output start m t radius scale shift bits exponent) v chart) ↔
        CriticalKernel.Bad (polynomial m sample t radius scale shift bits exponent) (m + 2) v chart := by
  let ops := program oldStart start m sample t radius scale shift bits exponent
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops
  have hw := wellFormed oldStart start m sample t radius scale shift bits exponent ht hs hm
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start ops hw
  have hin : ∀ i < start, wire i = X i := fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi
  have h := CriticalKernel.query_satisfiable wire start (m + 2) ops
    (output start m t radius scale shift bits exponent) v chart hi hw hr hin
    (output_lt oldStart start m sample t radius scale shift bits exponent)
  simpa only [wire, ops, symbolic_output oldStart start m sample t radius scale shift bits exponent ht hs hm] using h

noncomputable def kernelQuery (source radius scale shift bits exponent : List Bool → List Bool)
    (start m chart : List Bool → ℕ) (sample : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool) : List Gate :=
  CriticalKernel.query (start c) (m c + 2)
    (program (TermView.term (source c)).toData.size (start c) (m c) (sample c) (TermView.term (source c))
      (radius c) (scale c) (shift c) (bits c) (exponent c))
    (output (start c) (m c) (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c) (exponent c)) (v c) (chart c)

theorem kernelQuery_encode_mem_FP {source radius scale shift bits exponent : List Bool → List Bool}
    {start m chart : List Bool → ℕ} {sample : List Bool → ℤ} {v : List Bool → ℕ → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (kernelQuery source radius scale shift bits exponent start m chart sample v c)) ∈ FP :=
  CriticalKernel.query_encode_mem_FP hs (hm.add (UnaryFn.const 2)) (output_unary ht hs hm hR hF hb hN hE) hi
    (length_unary ht hm hR hF hb hN hE) (encode_mem_FP ht hs hm hsample hR hF hb hN hE) hv

noncomputable def kernelEmpty (source radius scale shift bits exponent : List Bool → List Bool)
    (start m chart : List Bool → ℕ) (sample : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  [decide (¬ Satisfiable (kernelQuery source radius scale shift bits exponent start m chart sample v c))]

theorem kernelEmpty_evaluator {source radius scale shift bits exponent : List Bool → List Bool}
    {start m chart : List Bool → ℕ} {sample : List Bool → ℤ} {v : List Bool → ℕ → ℤ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    SpaceFunction (kernelEmpty source radius scale shift bits exponent start m chart sample v) :=
  empty_generated (kernelQuery_encode_mem_FP ht hs hm hi hsample hR hF hb hN hE hv)

theorem kernelEmpty_correct (source radius scale shift bits exponent : List Bool → List Bool)
    (start m chart : List Bool → ℕ) (sample : List Bool → ℤ) (v : List Bool → ℕ → ℤ) (c : List Bool)
    (hs : (TermView.term (source c)).toData.size ≤ start c) (hm : m c + 2 ≤ start c) (hi : chart c < m c + 2) :
    kernelEmpty source radius scale shift bits exponent start m chart sample v c =
      [decide (¬ CriticalKernel.Bad (polynomial (m c) (sample c) (TermView.term (source c))
        (radius c) (scale c) (shift c) (bits c) (exponent c)) (m c + 2) (v c) (chart c))] := by
  simp only [kernelEmpty, kernelQuery,
    kernel_satisfiable _ _ _ _ _ _ _ _ _ _ _ _ (Term.arity_le_dataSize _) hs hm hi]

end LeanCanny.ETR.ComplexCircuit.BoundedSource
