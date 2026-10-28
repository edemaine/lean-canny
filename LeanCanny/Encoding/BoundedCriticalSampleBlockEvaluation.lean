/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockTerm

/-! # Block-term evaluation on arbitrary source records

The base sample belongs to the decoded source of the record. The record need
not be a canonical pair. Its complete contents still select the term, offset,
and free dimension, including when those controls retain query metadata.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockEvaluation
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleBlockSource BoundedCriticalSampleBlockEncoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleLabels.parameter

theorem denominator_nonzero (P : Readers) (o k : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (k u) → ℝ) (i : ℕ) :
    (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) ≠ 0 := by
  simp only [coordinate, Bool.false_eq_true, ite_false]
  split_ifs
  · simp only [MvPolynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]
  · rw [IndexedMultivariateRational.eval_parameter, environment_zero]
    have H := BoundedCriticalSampleTermCoordinates.denominator_nonzero P (pairFst u) [] p i
    simpa only [BoundedCriticalSampleLineCoordinates.base, Bool.false_eq_true, ite_false,
      BoundedCriticalSampleTermCoordinates.denominator, pairFst_pair] using H

theorem coordinate_eval (P : Readers) (o k : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (k u) → ℝ) (i : ℕ) :
    (coordinate P o k true u i).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) /
      (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ)
        (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) =
          assignment p.val (o u) (k u) y i := by
  simp only [coordinate, assignment, Bool.false_eq_true, ite_false, ite_true]
  split_ifs with hi
  · rw [MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, div_one, environment_variable]
  · rw [IndexedMultivariateRational.eval_parameter, IndexedMultivariateRational.eval_parameter,
      environment_zero]
    have H := BoundedCriticalSampleTermCoordinates.coordinate_eval P (pairFst u) [] p i
    simpa only [BoundedCriticalSampleLineCoordinates.base, Bool.false_eq_true, ite_true, ite_false,
      BoundedCriticalSampleTermCoordinates.numerator, BoundedCriticalSampleTermCoordinates.denominator,
      pairFst_pair] using H

theorem sign (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (k u) → ℝ) :
    SignType.sign ((BoundedCriticalSampleBlockTerm.polynomial P read o k u).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y)) =
        SignType.sign ((TermView.term (read u)).eval (assignment p.val (o u) (k u) y)) := by
  let v := environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y
  let env := fun i => (coordinate P o k true u i).eval₂ (Int.castRingHom ℝ) v /
    (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ) v
  have H := IndexedMultivariateRational.sign_eval₂_cleared (Int.castRingHom ℝ) v
    (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount ((source read).syntax u).toData.size
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (coordinate P o k true u) (coordinate P o k false u)
    (fun r _ i _ => BivariateRationalTermReader.exponent_bound (source read) u r i)
    (fun i _ => denominator_nonzero P o k u p y i)
  have HS := ((source read).syntax u).eval₂_indexed_source env _ ((source read).scope u)
  have HE : env = assignment p.val (o u) (k u) y := funext (fun i => coordinate_eval P o k u p y i)
  refine H.trans ((congrArg SignType.sign HS).trans ?_)
  rw [HE]
  rfl

end LeanCanny.Encoding.BoundedCriticalSampleBlockEvaluation
