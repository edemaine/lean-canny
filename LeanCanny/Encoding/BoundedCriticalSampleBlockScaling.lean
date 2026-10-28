/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockEvaluation
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry
public import LeanCanny.Algebra.ParameterSpatialSpecialization
public import LeanCanny.Geometry.ScaledCriticalSystem
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # Exact constant scaling of actual-parent block polynomials

At a fixed actual parent, every denominator is constant in the free block.
The cleared polynomial is therefore a positive constant times the original
term with its other coordinates frozen. This preserves every critical root
and its regularity, including singular or positive-dimensional critical sets.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockScaling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open BoundedCriticalSampleBlockSource BoundedCriticalSampleBlockEncoding
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleLabels.parameter

theorem denominator_constant (P : Readers) (o k : List Bool → ℕ) (u : List Bool)
    (t : ℝ) (y z : Fin (k u) → ℝ) (i : ℕ) :
    (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ) (environment _ t y) =
      (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ) (environment _ t z) := by
  simp only [coordinate, Bool.false_eq_true, ite_false]
  split_ifs
  · simp only [eval₂_one]
  · rw [IndexedMultivariateRational.eval_parameter, IndexedMultivariateRational.eval_parameter,
      environment_zero, environment_zero]

noncomputable def scale (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u)) : ℝ :=
  ∏ i ∈ Finset.range (Nat.fromBitsLE ((source read).arity u)),
    (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val 0) ^
        (2 * ((source read).syntax u).toData.size)

attribute [local irreducible] scale

theorem scale_pos (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u)) :
    0 < scale P read o k u p := by
  unfold scale
  apply Finset.prod_pos
  intro i _
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero
    (BoundedCriticalSampleBlockEvaluation.denominator_nonzero P o k u p 0 i)) _

theorem eval (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (k u) → ℝ) :
    (BoundedCriticalSampleBlockTerm.polynomial P read o k u).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) =
        scale P read o k u p * (TermView.term (read u)).eval (assignment p.val (o u) (k u) y) := by
  have H := IndexedMultivariateRational.eval₂_cleared (Int.castRingHom ℝ)
    (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y)
    (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount
    (2 * ((source read).syntax u).toData.size) ((source read).syntax u).monomialCoefficient
    ((source read).syntax u).monomialExponent (coordinate P o k true u) (coordinate P o k false u)
    (fun r _ i _ => BivariateRationalTermReader.exponent_bound (source read) u r i)
    (fun i _ => BoundedCriticalSampleBlockEvaluation.denominator_nonzero P o k u p y i)
  change _ = _ * _ at H
  rw [show (∏ i ∈ Finset.range (Nat.fromBitsLE ((source read).arity u)),
      (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ)
        (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) ^
          (2 * ((source read).syntax u).toData.size)) = scale P read o k u p from by
    unfold scale
    apply Finset.prod_congr rfl
    intro i _
    rw [denominator_constant P o k u _ y 0 i]] at H
  rw [BoundedCriticalSampleBlockTerm.polynomial, H]
  congr 1
  let env := fun i => (coordinate P o k true u i).eval₂ (Int.castRingHom ℝ)
    (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) /
      (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ)
        (environment _ (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y)
  have HS := ((source read).syntax u).eval₂_indexed_source env _ ((source read).scope u)
  have HE : env = assignment p.val (o u) (k u) y :=
    funext (fun i => BoundedCriticalSampleBlockEvaluation.coordinate_eval P o k u p y i)
  exact HS.trans (by rw [HE]; rfl)

noncomputable def original {n : ℕ} (t : Term) (p : Fin n → ℝ) (o k : ℕ) :
    MvPolynomial (Fin k) ℝ :=
  t.eval (fun i => if hi : InBlock o k i then X ⟨i - o, by unfold InBlock at hi; omega⟩
    else C (Formula.extend p i))

theorem eval_original {n : ℕ} (t : Term) (p : Fin n → ℝ) (o k : ℕ) (y : Fin k → ℝ) :
    (original t p o k).eval y = t.eval (assignment p o k y) := by
  rw [original, Term.eval_hom]
  apply Term.eval_congr
  intro i _
  by_cases hi : InBlock o k i <;> simp only [hi, dite_true, dite_false, eval_X, eval_C, assignment]

noncomputable def specialized (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u)) : MvPolynomial (Fin (k u)) ℝ :=
  ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
    (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val
    (BoundedCriticalSampleBlockTerm.polynomial P read o k u)

theorem specialized_eq (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u)) :
    specialized P read o k u p =
      C (scale P read o k u p) * original (TermView.term (read u)) p.val (o u) (k u) := by
  apply MvPolynomial.funext
  intro y
  rw [specialized, ParameterSpatialSpecialization.eval_specialize,
    ← BoundedCriticalSampleBlockCriticalGeometry.environment_eq_cons, eval, eval_mul, eval_C, eval_original]

theorem critical_zero_iff (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u))
    (b : Fin (k u)) (v : Fin (k u) → ℝ) (y : Fin (k u) → ℝ) :
    (∀ i, (ProjectionCriticalFamily.spatialEquation (specialized P read o k u p) b v i).eval y = 0) ↔
      ∀ i, (ProjectionCriticalFamily.spatialEquation
        (original (TermView.term (read u)) p.val (o u) (k u)) b v i).eval y = 0 := by
  rw [specialized_eq]
  exact Geometry.ScaledCriticalSystem.zero_iff (RingHom.id ℝ) _ b v _ (ne_of_gt (scale_pos P read o k u p)) y

theorem critical_regular_iff (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples P (pairFst u))
    (b : Fin (k u)) (v : Fin (k u) → ℝ) (y : Fin (k u) → ℝ) :
    (fderiv ℝ (fun z => fun i =>
      (ProjectionCriticalFamily.spatialEquation (specialized P read o k u p) b v i).eval z) y).IsInvertible ↔
      (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation
        (original (TermView.term (read u)) p.val (o u) (k u)) b v i).eval z) y).IsInvertible := by
  rw [specialized_eq]
  simpa only [eval₂_id] using Geometry.ScaledCriticalSystem.regular_iff (RingHom.id ℝ) _ b v (scale P read o k u p)
    (ne_of_gt (scale_pos P read o k u p)) y

end LeanCanny.Encoding.BoundedCriticalSampleBlockScaling
