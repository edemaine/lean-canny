/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleHashEnumeration
public import LeanCanny.Algebra.FunctionBasisProbe

/-! # Pointwise feature-sign recovery on actual critical samples

Two weighted Gram determinant coefficients recover a feature's sign at a
sample. The denominator is nonzero because the selected integer hash is
injective on the exact filtered sample set.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSamplePointProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleBasisPencil
open scoped Classical

noncomputable def hashFunction (P : Readers) (c : List Bool) : BoundedCriticalSampleRecordSpan.Root P c → ℚ :=
  fun x => BoundedCriticalSampleHashChoice.hash P c x

noncomputable def matrix (P : Readers) (c : List Bool) (s : BoundedCriticalSampleRecordSpan.Root P c → ℚ) (h : ℤ) :
    Matrix (Fin (BoundedCriticalSampleCount.count P c)) (Fin (BoundedCriticalSampleCount.count P c)) ℚ[X] :=
  fun i j => C ((h : ℚ) * BoundedCriticalSampleBasisGram.gram P c i j - weighted P c (hashFunction P c) i j) +
    C (weighted P c s i j) * X

theorem matrix_eq (P : Readers) (c : List Bool) (s : BoundedCriticalSampleRecordSpan.Root P c → ℚ) (h : ℤ) :
    matrix P c s h = FunctionBasisProbe.matrix (square P c) (hashFunction P c ∘ rootEquiv P c)
      (s ∘ rootEquiv P c) (h : ℚ) := by
  unfold matrix FunctionBasisProbe.matrix
  rw [gram_eq, weighted_eq, weighted_eq]

theorem hashFunction_injective (P : Readers) (c : List Bool) : Function.Injective (hashFunction P c ∘ rootEquiv P c) := by
  intro i j he
  apply (rootEquiv P c).injective
  apply BoundedCriticalSampleHashChoice.hash_injective P c
  exact Int.cast_injective he

theorem denominator_nonzero (P : Readers) (c : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    (matrix P c (fun _ => 1) (BoundedCriticalSampleHashChoice.hash P c x)).det.coeff 1 ≠ 0 := by
  rw [matrix_eq]
  have H := FunctionBasisProbe.denominator_nonzero (square P c) (hashFunction P c ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

theorem sign_at_root (P : Readers) (c : List Bool) (s : BoundedCriticalSampleRecordSpan.Root P c → ℚ)
    (x : BoundedCriticalSampleRecordSpan.Root P c) :
    SignType.sign ((matrix P c s (BoundedCriticalSampleHashChoice.hash P c x)).det.coeff 1) *
      SignType.sign ((matrix P c (fun _ => 1) (BoundedCriticalSampleHashChoice.hash P c x)).det.coeff 1) = SignType.sign (s x) := by
  rw [matrix_eq, matrix_eq]
  have H := FunctionBasisProbe.sign_ratio (square P c) (hashFunction P c ∘ rootEquiv P c) (s ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

end LeanCanny.Encoding.BoundedCriticalSamplePointProbe
