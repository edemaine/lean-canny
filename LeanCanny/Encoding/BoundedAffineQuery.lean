/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedSourceWriter

/-! # Affine critical-kernel queries for the actual bounded regular source

The source, its degree and coefficient bounds, and every large scale come
from the original encoded term. Correctness identifies the old finite sweep
predicate, including its value, gradient and Hessian conditions.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAffineQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open BoundedSourceWriter FermatSweepCertificate
open scoped Classical

noncomputable def query (P : Readers) (chart : List Bool → ℕ) (c : List Bool) : List Gate :=
  CriticalKernel.query (start P c) (P.dim c + 3) (program P c) (output P c)
    (FermatAffineQuery.direction (fun c => P.dim c + 2) (degree P) P.record c) (chart c)

theorem encode_mem_FP {P : Readers} (h : P.PolyTime) {chart : List Bool → ℕ} (hi : UnaryFn chart) :
    (fun c => encode (query P chart c)) ∈ FP :=
  CriticalKernel.query_encode_mem_FP (start_unary h) (h.dim.add (UnaryFn.const 3)) (output_unary h) hi
    (length_unary h) (BoundedSourceWriter.encode_mem_FP h)
    (FermatAffineQuery.directionLiteral_mem_FP (h.dim.add (UnaryFn.const 2)) (degree_binary h) h.record)

theorem query_correct (P : Readers) (chart : List Bool → ℕ) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hi : chart c < P.dim c + 3) :
    Satisfiable (query P chart c) ↔
      AffineBad ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c) ⟨chart c, hi⟩ := by
  have hk := BoundedSource.kernel_satisfiable (size P c) (start P c) (P.dim c + 1) (sample P c)
    (TermView.term (P.source c)) (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
    (degree P c - 1).bits (regularizationExponent P c).bits
    (FermatAffineQuery.direction (fun c => P.dim c + 2) (degree P) P.record c) (chart c)
    (Term.arity_le_dataSize _) (Nat.le_max_left ..) (Nat.le_max_right ..) hi
  have hf := CriticalKernel.bad_iff_finite (n := P.dim c + 2)
    (BoundedSource.polynomial (P.dim c + 1) (sample P c) (TermView.term (P.source c))
      (2 * P.radius c).bits (scaleExponent P c).bits (shiftExponent P c).bits
      (degree P c - 1).bits (regularizationExponent P c).bits)
    (sampledPolynomial ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c))
    (polynomial_source_identity P c ht)
    (FermatAffineQuery.direction (fun c => P.dim c + 2) (degree P) P.record c) ⟨chart c, hi⟩
  have ha := finite_bad_iff_affine ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c)
    (FermatAffineQuery.direction (fun c => P.dim c + 2) (degree P) P.record c)
    (fun j => FermatAffineQuery.direction_eq (fun c => P.dim c + 2) (degree P) P.record c j) ⟨chart c, hi⟩
  exact hk.trans (hf.trans ha)

noncomputable def empty (P : Readers) (chart : List Bool → ℕ) (c : List Bool) : List Bool :=
  [decide (¬ Satisfiable (query P chart c))]

theorem empty_evaluator {P : Readers} (h : P.PolyTime) {chart : List Bool → ℕ} (hi : UnaryFn chart) :
    SpaceFunction (empty P chart) := empty_generated (encode_mem_FP h hi)

theorem empty_correct (P : Readers) (chart : List Bool → ℕ) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hi : chart c < P.dim c + 3) :
    empty P chart c =
      [decide (¬ AffineBad ((lower P c).map (Int.castRingHom ℚ)) (leading P c : ℚ) (degree P c) (P.record c) ⟨chart c, hi⟩)] := by
  simp only [empty, query_correct P chart c ht hi]

theorem empty_precomp (P : Readers) (f : List Bool → List Bool) (chart : List Bool → ℕ) (c : List Bool) :
    empty (P.precomp f) chart c = empty P (fun _ => chart c) (f c) := rfl

end LeanCanny.Encoding.BoundedAffineQuery
