/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionHashEnumeration
public import LeanCanny.Algebra.FunctionBasisProbe

/-! # Derivative-sign recovery at an enumerated projection-root hash

Two weighted Gram determinant coefficients determine a feature's sign at
one root. The denominator is nonzero because the selected hash separates
the roots. This is the correctness identity for a native signature reader;
native feature-weighted entries are supplied by `BoundedProjectionFeatureMoments`.
`BoundedProjectionSignatureRead` supplies native determinant-coefficient sign
evaluation and the resulting streamed derivative-sign reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionSignatureProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedProjectionBasisPencil
open scoped Classical

noncomputable def hashFunction (P : Readers) (c : List Bool) : BoundedProjectionRecordSpan.Root P c → ℚ :=
  fun x => BoundedProjectionHashChoice.hash P c x

noncomputable def matrix (P : Readers) (c : List Bool) (s : BoundedProjectionRecordSpan.Root P c → ℚ) (h : ℤ) :
    Matrix (Fin (BoundedProjectionRootCount.count P c)) (Fin (BoundedProjectionRootCount.count P c)) ℚ[X] :=
  fun i j => C ((h : ℚ) * BoundedProjectionBasisGram.gram P c i j - weighted P c (hashFunction P c) i j) +
    C (weighted P c s i j) * X

theorem matrix_eq (P : Readers) (c : List Bool) (s : BoundedProjectionRecordSpan.Root P c → ℚ) (h : ℤ) :
    matrix P c s h = FunctionBasisProbe.matrix (square P c) (hashFunction P c ∘ rootEquiv P c)
      (s ∘ rootEquiv P c) (h : ℚ) := by
  unfold matrix FunctionBasisProbe.matrix
  rw [gram_eq, weighted_eq, weighted_eq]

theorem hashFunction_injective (P : Readers) (c : List Bool) : Function.Injective (hashFunction P c ∘ rootEquiv P c) := by
  intro i j he
  apply (rootEquiv P c).injective
  apply BoundedProjectionHashChoice.hash_injective P c
  exact Int.cast_injective he

theorem denominator_nonzero (P : Readers) (c : List Bool) (x : BoundedProjectionRecordSpan.Root P c) :
    (matrix P c (fun _ => 1) (BoundedProjectionHashChoice.hash P c x)).det.coeff 1 ≠ 0 := by
  rw [matrix_eq]
  have H := FunctionBasisProbe.denominator_nonzero (square P c) (hashFunction P c ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

theorem sign_at_root (P : Readers) (c : List Bool) (s : BoundedProjectionRecordSpan.Root P c → ℚ)
    (x : BoundedProjectionRecordSpan.Root P c) :
    SignType.sign ((matrix P c s (BoundedProjectionHashChoice.hash P c x)).det.coeff 1) *
      SignType.sign ((matrix P c (fun _ => 1) (BoundedProjectionHashChoice.hash P c x)).det.coeff 1) = SignType.sign (s x) := by
  rw [matrix_eq, matrix_eq]
  have H := FunctionBasisProbe.sign_ratio (square P c) (hashFunction P c ∘ rootEquiv P c) (s ∘ rootEquiv P c)
    ((rootEquiv P c).symm x) (square_det_ne_zero P c) (hashFunction_injective P c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem signature_at_ordinal (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    SignType.sign ((matrix P c (fun x => (BoundedProjectionMoments.signature P c x d : ℚ))
      (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) *
      SignType.sign ((matrix P c (fun _ => 1)
        (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) =
      BoundedProjectionMoments.signature P c (BoundedProjectionHashEnumeration.root P c r) d := by
  have H := sign_at_root P c (fun x => (BoundedProjectionMoments.signature P c x d : ℚ))
    (BoundedProjectionHashEnumeration.root P c r)
  rw [BoundedProjectionHashEnumeration.hash_root, sign_cast] at H
  exact H

end LeanCanny.Encoding.BoundedProjectionSignatureProbe
