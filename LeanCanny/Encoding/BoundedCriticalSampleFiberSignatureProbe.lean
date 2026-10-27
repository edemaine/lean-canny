/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberHashEnumeration
public import LeanCanny.Algebra.FunctionBasisProbe

/-! # Derivative-sign recovery at an enumerated fiber-root hash

Two weighted Gram determinant coefficients determine a feature's sign at
one root. The denominator is nonzero because the selected hash separates
the roots. This is the correctness identity for a native signature reader;
native feature-weighted entries are supplied by `BoundedCriticalSampleFiberFeatureMoments`.
`BoundedCriticalSampleFiberSignatureRead` supplies native determinant-coefficient sign
evaluation and the resulting streamed derivative-sign reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberSignatureProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleFiberBasisPencil
open scoped Classical

noncomputable def hashFunction (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : BoundedCriticalSampleFiberRecordSpan.Root P F c → ℚ :=
  fun x => BoundedCriticalSampleFiberHashChoice.hash P F c x

noncomputable def matrix (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (s : BoundedCriticalSampleFiberRecordSpan.Root P F c → ℚ) (h : ℤ) :
    Matrix (Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) (Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) ℚ[X] :=
  fun i j => C ((h : ℚ) * BoundedCriticalSampleFiberBasisGram.gram P F c i j - weighted P F c (hashFunction P F c) i j) +
    C (weighted P F c s i j) * X

theorem matrix_eq (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (s : BoundedCriticalSampleFiberRecordSpan.Root P F c → ℚ) (h : ℤ) :
    matrix P F c s h = FunctionBasisProbe.matrix (square P F c) (hashFunction P F c ∘ rootEquiv P F c)
      (s ∘ rootEquiv P F c) (h : ℚ) := by
  unfold matrix FunctionBasisProbe.matrix
  rw [gram_eq, weighted_eq, weighted_eq]

theorem hashFunction_injective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Injective (hashFunction P F c ∘ rootEquiv P F c) := by
  intro i j he
  apply (rootEquiv P F c).injective
  apply BoundedCriticalSampleFiberHashChoice.hash_injective P F c
  exact Int.cast_injective he

theorem denominator_nonzero (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    (matrix P F c (fun _ => 1) (BoundedCriticalSampleFiberHashChoice.hash P F c x)).det.coeff 1 ≠ 0 := by
  rw [matrix_eq]
  have H := FunctionBasisProbe.denominator_nonzero (square P F c) (hashFunction P F c ∘ rootEquiv P F c)
    ((rootEquiv P F c).symm x) (square_det_ne_zero P F c) (hashFunction_injective P F c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

theorem sign_at_root (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (s : BoundedCriticalSampleFiberRecordSpan.Root P F c → ℚ)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    SignType.sign ((matrix P F c s (BoundedCriticalSampleFiberHashChoice.hash P F c x)).det.coeff 1) *
      SignType.sign ((matrix P F c (fun _ => 1) (BoundedCriticalSampleFiberHashChoice.hash P F c x)).det.coeff 1) = SignType.sign (s x) := by
  rw [matrix_eq, matrix_eq]
  have H := FunctionBasisProbe.sign_ratio (square P F c) (hashFunction P F c ∘ rootEquiv P F c) (s ∘ rootEquiv P F c)
    ((rootEquiv P F c).symm x) (square_det_ne_zero P F c) (hashFunction_injective P F c)
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hashFunction] using H

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem signature_at_ordinal (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c))
    (d : BoundedCriticalSampleFiberThom.Feature F c) :
    SignType.sign ((matrix P F c (fun x => (BoundedCriticalSampleFiberThom.signature P F c x d : ℚ))
      (BoundedCriticalSampleFiberHashEnumeration.value P F (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) *
      SignType.sign ((matrix P F c (fun _ => 1)
        (BoundedCriticalSampleFiberHashEnumeration.value P F (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) =
      BoundedCriticalSampleFiberThom.signature P F c (BoundedCriticalSampleFiberHashEnumeration.root P F c r) d := by
  have H := sign_at_root P F c (fun x => (BoundedCriticalSampleFiberThom.signature P F c x d : ℚ))
    (BoundedCriticalSampleFiberHashEnumeration.root P F c r)
  rw [BoundedCriticalSampleFiberHashEnumeration.hash_root, sign_cast] at H
  exact H

end LeanCanny.Encoding.BoundedCriticalSampleFiberSignatureProbe
