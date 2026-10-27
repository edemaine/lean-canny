/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockCritical

/-! # Actual slice semantics of the constructed block critical system

Specialization uses the original actual sample parameter. The resulting
spatial polynomial has exactly the original term's zero set on the free
coordinate block, and the constructed rows are its critical equations.
These identities do not assume that the candidate critical system is finite
or regular; selecting such directions remains a later obligation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter MvPolynomial
open BoundedCriticalSampleBlockSource
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleBlockTerm.polynomial

theorem environment_eq_cons {n : ℕ} (t : ℝ) (y : Fin n → ℝ) : environment n t y = Fin.cons t y := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [environment_zero, Fin.cons_zero]
  · simp only [environment, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel, Fin.cons_succ]

noncomputable def samplePolynomial (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : MvPolynomial (Fin (k (pair c r))) ℝ :=
  ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val
    (BoundedCriticalSampleBlockTerm.polynomial P read o k (pair c r))

theorem sign_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) :
    SignType.sign ((samplePolynomial P read o k c r x).eval y) =
      SignType.sign ((TermView.term (read (pair c r))).eval (assignment x.val (o (pair c r)) (k (pair c r)) y)) := by
  rw [samplePolynomial, ParameterSpatialSpecialization.eval_specialize, ← environment_eq_cons]
  exact BoundedCriticalSampleBlockTerm.sign_sample P read o k c r x y

theorem zero_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) :
    (samplePolynomial P read o k c r x).eval y = 0 ↔
      (TermView.term (read (pair c r))).eval (assignment x.val (o (pair c r)) (k (pair c r)) y) = 0 := by
  rw [← sign_eq_zero_iff, sign_sample, sign_eq_zero_iff]

theorem zero_finite_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ)
    (hk : o (pair c r) + k (pair c r) ≤ P.dim c + 4) :
    (samplePolynomial P read o k c r x).eval y = 0 ↔
      (TermView.term (read (pair c r))).eval
        (Formula.extend (finiteAssignment x.val (o (pair c r)) (k (pair c r)) y)) = 0 := by
  rw [zero_sample, assignment_finite x.val _ _ y hk]

theorem sample_equation (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (b i : Fin (k (pair c r))) :
    ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val
      (BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits (pair c r) b i) =
        ProjectionCriticalFamily.spatialEquation (samplePolynomial P read o k c r x) b
          (fun j => (BoundedCriticalSampleBlockCriticalSource.direction k w bits (pair c r) j : ℝ)) i :=
  BoundedCriticalSampleBlockCriticalSource.specialize_polynomial P read o k w bits (pair c r) b i _

theorem sample_equations_zero_iff (P : Readers) (read : List Bool → List Bool) (o k w : List Bool → ℕ)
    (bits : List Bool → List Bool) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (b : Fin (k (pair c r))) (y : Fin (k (pair c r)) → ℝ) :
    (∀ i, (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
      (BoundedCriticalSampleLabels.parameter P c x).val
      (BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits (pair c r) b i)).eval y = 0) ↔
        (samplePolynomial P read o k c r x).eval y = 0 ∧ ∀ i, i ≠ b →
          (pderiv i (samplePolynomial P read o k c r x)).eval y =
            (BoundedCriticalSampleBlockCriticalSource.direction k w bits (pair c r) i : ℝ) *
              (pderiv b (samplePolynomial P read o k c r x)).eval y := by
  simp only [sample_equation]
  constructor
  · intro h
    refine ⟨by simpa only [ProjectionCriticalFamily.spatialEquation, ite_true] using h b, ?_⟩
    intro i hi
    simpa only [ProjectionCriticalFamily.spatialEquation, hi, ite_false, eval_sub, eval_mul, eval_C, sub_eq_zero] using h i
  · rintro ⟨hp, hd⟩ i
    by_cases hi : i = b
    · simpa only [ProjectionCriticalFamily.spatialEquation, hi, ite_true] using hp
    · simp only [ProjectionCriticalFamily.spatialEquation, hi, ite_false, eval_sub, eval_mul, eval_C, hd i hi, sub_self]

end LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry
