/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedProjectionTestMoments
open scoped Classical BigOperators

noncomputable def feature (P : Readers) (T : Test) (c : List Bool) : BoundedProjectionRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] BoundedProjectionTestProbe.linear BoundedProjectionTestMoments.moment

theorem linear_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionTestProbe.linear P T (BoundedProjectionProbeSource.row P c h 0 i j) : ℚ) =
      BoundedProjectionBasisPencil.weighted P c (feature P T c) i j := by
  have hq : BoundedProjectionTestProbe.linearQuery (BoundedProjectionProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedProjectionTestProbe.linearQuery, BoundedProjectionProbeSource.row,
      BoundedProjectionProbeSource.context, BoundedProjectionProbeEntries.context, BoundedProjectionProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, BoundedProjectionProbeSource.hash_original]
  rw [BoundedProjectionTestProbe.linear, hq, moment_packet]
  unfold BoundedProjectionBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    ((BoundedProjectionTestProbe.matrix P T (BoundedProjectionProbeSource.context P c h 0)).submatrix
      (BoundedProjectionProbeSource.indexEquiv P c h 0) (BoundedProjectionProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedProjectionSignatureProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedProjectionTestProbe.matrix, BoundedProjectionProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedProjectionProbeEntries.constant P (BoundedProjectionProbeSource.row P c h 0 i j) : ℚ) +
    C (BoundedProjectionTestProbe.linear P T (BoundedProjectionProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [BoundedProjectionProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    (BoundedProjectionTestProbe.matrix P T (BoundedProjectionProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (BoundedProjectionSignatureProbe.matrix P c (feature P T c) h).det := by
  let A := BoundedProjectionTestProbe.matrix P T (BoundedProjectionProbeSource.context P c h 0)
  let e := BoundedProjectionProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (BoundedProjectionTestProbe.firstCoefficient P T (BoundedProjectionProbeSource.context P c h 0)) =
      SignType.sign ((BoundedProjectionSignatureProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (BoundedProjectionTestProbe.firstCoefficient P T (BoundedProjectionProbeSource.context P c h 0) : ℚ) =
      (BoundedProjectionSignatureProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold BoundedProjectionTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Readers) (T : Test) (c : List Bool) (x : BoundedProjectionRecordSpan.Root P c) :
    SignType.sign (BoundedProjectionTestProbe.firstCoefficient P T
        (BoundedProjectionProbeSource.context P c (BoundedProjectionHashChoice.hash P c x) 0)) *
      SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P true
        (BoundedProjectionProbeSource.context P c (BoundedProjectionHashChoice.hash P c x) 0)) = sign T c x.val := by
  rw [sign_packet, BoundedProjectionProbeSource.sign_packet P true c _ ⟨0, Nat.succ_pos _⟩]
  simp only [BoundedProjectionProbeSource.featureFunction, ↓reduceIte]
  have H := BoundedProjectionSignatureProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.BoundedProjectionTestProbeSource
