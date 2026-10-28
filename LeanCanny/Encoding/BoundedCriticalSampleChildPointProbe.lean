/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildHashEnumeration
public import LeanCanny.Algebra.FunctionBasisProbe

/-! # Pointwise feature-sign recovery on regular child roots

Two weighted Gram determinant coefficients recover a feature's sign at a
sample. The denominator is nonzero because the selected integer hash is
injective on the exact filtered sample set.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildPointProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildBasisPencil
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def hashFunction (P : Inputs) (c : List Bool) : BoundedCriticalSampleChildRecordSpan.Root P c → ℚ :=
  fun x => BoundedCriticalSampleChildHashChoice.hash P c x

noncomputable def matrix (P : Inputs) (c : List Bool) (s : BoundedCriticalSampleChildRecordSpan.Root P c → ℚ) (h : ℤ) :
    Matrix (Fin (BoundedCriticalSampleChildRegularCount.count P c)) (Fin (BoundedCriticalSampleChildRegularCount.count P c)) ℚ[X] :=
  fun i j => C ((h : ℚ) * BoundedCriticalSampleChildBasisGram.gram P c i j - weighted P c (hashFunction P c) i j) +
    C (weighted P c s i j) * X

theorem matrix_eq (P : Inputs) (c : List Bool) (s : BoundedCriticalSampleChildRecordSpan.Root P c → ℚ) (h : ℤ) :
    matrix P c s h = FunctionBasisProbe.matrix (square P c) (hashFunction P c ∘ rootEquiv P c)
      (s ∘ rootEquiv P c) (h : ℚ) := by
  unfold matrix FunctionBasisProbe.matrix
  rw [gram_eq, weighted_eq, weighted_eq]

theorem hashFunction_injective (P : Inputs) (c : List Bool) : Function.Injective (hashFunction P c ∘ rootEquiv P c) := by
  intro i j he
  apply (rootEquiv P c).injective
  apply BoundedCriticalSampleChildHashChoice.hash_injective P c
  exact Int.cast_injective he

theorem denominator_nonzero (P : Inputs) (c : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    (matrix P c (fun _ => 1) (BoundedCriticalSampleChildHashChoice.hash P c x)).det.coeff 1 ≠ 0 := by
  rw [matrix_eq]
  have H := FunctionBasisProbe.denominator_nonzero (square P c) (hashFunction P c ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

theorem sign_at_root (P : Inputs) (c : List Bool) (s : BoundedCriticalSampleChildRecordSpan.Root P c → ℚ)
    (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    SignType.sign ((matrix P c s (BoundedCriticalSampleChildHashChoice.hash P c x)).det.coeff 1) *
      SignType.sign ((matrix P c (fun _ => 1) (BoundedCriticalSampleChildHashChoice.hash P c x)).det.coeff 1) = SignType.sign (s x) := by
  rw [matrix_eq, matrix_eq]
  have H := FunctionBasisProbe.sign_ratio (square P c) (hashFunction P c ∘ rootEquiv P c) (s ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildPointProbe
