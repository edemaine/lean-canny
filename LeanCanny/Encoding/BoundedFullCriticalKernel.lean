/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.ETR.ComplexCriticalKernelFinite

/-! # Native critical-kernel queries for the full regular source

The full varying-coordinate source program is differentiated directly.
Normalized kernel charts test singular critical points of an integer linear
projection, with native encoders for the shared Hessian programs. The exact
finite-coordinate interpretation discards the unused initial frame slots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullCriticalKernel
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open BoundedFullWriter
open scoped Classical

noncomputable def polynomial (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c + 4)) ℂ :=
  (BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)).map (Int.castRingHom ℂ)

noncomputable def query (P : Readers) (v : ℕ → ℤ) (chart : ℕ) (c : List Bool) : List Gate :=
  CriticalKernel.query (start P c) (P.dim c + 4) (program P c) (output P c) v chart

theorem polynomial_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    polynomial (P.comp f) c = polynomial P (f c) := rfl

theorem query_comp (P : Readers) (f : List Bool → List Bool) (v : ℕ → ℤ) (chart : ℕ) (c : List Bool) :
    query (P.comp f) v chart c = query P v chart (f c) := rfl

theorem encode_mem_FP {P : Readers} {v : List Bool → ℕ → ℤ} {chart : List Bool → ℕ}
    (h : P.PolyTime) (hi : UnaryFn chart)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (query P (v c) (chart c) c)) ∈ FP :=
  CriticalKernel.query_encode_mem_FP (start_unary h) (h.dim.add (UnaryFn.const 4)) (output_unary h) hi
    (length_unary h) (BoundedFullWriter.encode_mem_FP h) hv

theorem correct (P : Readers) (c : List Bool) (v : ℕ → ℤ) (chart : Fin (P.dim c + 4))
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Satisfiable (query P v chart.val c) ↔ CriticalKernel.FiniteBad (polynomial P c) v chart := by
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c)
  have hw := wellFormed P c
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) (start P c) (program P c) hw
  have hin : ∀ i < start P c, wire i = X i :=
    fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi
  have hmodel : (wire (output P c)).map (Int.castRingHom ℂ) = rename Fin.val (polynomial P c) := by
    rw [show wire (output P c) = rename Fin.val
      (BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)) from
        BoundedFullGeometry.source_identity P c ht, map_rename]
    rfl
  exact (CriticalKernel.query_satisfiable wire (start P c) (P.dim c + 4) (program P c) (output P c)
    v chart.val chart.isLt hw hr hin (output_lt P c)).trans
      (CriticalKernel.bad_iff_finite _ _ hmodel v chart)

theorem bad_evaluator {P : Readers} {v : List Bool → ℕ → ℤ} {chart : (c : List Bool) → Fin (P.dim c + 4)}
    (h : P.PolyTime) (hi : UnaryFn (fun c => (chart c).val))
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (CriticalKernel.FiniteBad (polynomial P c) (v c) (chart c))]) := by
  apply (feasible_generated (encode_mem_FP h hi hv)).congr
  funext c
  rw [correct P c (v c) (chart c) (ht c)]

theorem empty_evaluator {P : Readers} {v : List Bool → ℕ → ℤ} {chart : (c : List Bool) → Fin (P.dim c + 4)}
    (h : P.PolyTime) (hi : UnaryFn (fun c => (chart c).val))
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (¬ CriticalKernel.FiniteBad (polynomial P c) (v c) (chart c))]) := by
  apply (empty_generated (encode_mem_FP h hi hv)).congr
  funext c
  rw [correct P c (v c) (chart c) (ht c)]

end LeanCanny.Encoding.BoundedFullCriticalKernel
