/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildHashEnumeration
public import LeanCanny.Algebra.FunctionBasisProbe

/-! # Pointwise feature-sign recovery on regular child roots

Two weighted Gram determinant coefficients recover a feature's sign at a
sample. The denominator is nonzero because the selected integer hash is
injective on the exact filtered sample set.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildPointProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildBasisPencil
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

noncomputable def hashFunction (P : Inputs) (c : List Bool) : RationalParentChildRecordSpan.Root P c → ℚ :=
  fun x => RationalParentChildHashChoice.hash P c x

noncomputable def matrix (P : Inputs) (c : List Bool) (s : RationalParentChildRecordSpan.Root P c → ℚ) (h : ℤ) :
    Matrix (Fin (RationalParentChildRegularCount.count P c)) (Fin (RationalParentChildRegularCount.count P c)) ℚ[X] :=
  fun i j => C ((h : ℚ) * RationalParentChildBasisGram.gram P c i j - weighted P c (hashFunction P c) i j) +
    C (weighted P c s i j) * X

theorem matrix_eq (P : Inputs) (c : List Bool) (s : RationalParentChildRecordSpan.Root P c → ℚ) (h : ℤ) :
    matrix P c s h = FunctionBasisProbe.matrix (square P c) (hashFunction P c ∘ rootEquiv P c)
      (s ∘ rootEquiv P c) (h : ℚ) := by
  unfold matrix FunctionBasisProbe.matrix
  rw [gram_eq, weighted_eq, weighted_eq]

theorem hashFunction_injective (P : Inputs) (c : List Bool) : Function.Injective (hashFunction P c ∘ rootEquiv P c) := by
  intro i j he
  apply (rootEquiv P c).injective
  apply RationalParentChildHashChoice.hash_injective P c
  exact Int.cast_injective he

theorem denominator_nonzero (P : Inputs) (c : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    (matrix P c (fun _ => 1) (RationalParentChildHashChoice.hash P c x)).det.coeff 1 ≠ 0 := by
  rw [matrix_eq]
  have H := FunctionBasisProbe.denominator_nonzero (square P c) (hashFunction P c ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

theorem sign_at_root (P : Inputs) (c : List Bool) (s : RationalParentChildRecordSpan.Root P c → ℚ)
    (x : RationalParentChildRecordSpan.Root P c) :
    SignType.sign ((matrix P c s (RationalParentChildHashChoice.hash P c x)).det.coeff 1) *
      SignType.sign ((matrix P c (fun _ => 1) (RationalParentChildHashChoice.hash P c x)).det.coeff 1) = SignType.sign (s x) := by
  rw [matrix_eq, matrix_eq]
  have H := FunctionBasisProbe.sign_ratio (square P c) (hashFunction P c ∘ rootEquiv P c) (s ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

end LeanCanny.Encoding.RationalParentChildPointProbe
