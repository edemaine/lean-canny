/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleIndexedProbe
public import LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeFrame
public import LeanCanny.Encoding.BoundedCriticalSampleTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleTestMoments
open scoped Classical BigOperators

noncomputable def feature (P : Readers) (T : Test) (c d : List Bool) : BoundedCriticalSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] BoundedCriticalSampleIndexedProbe.linear BoundedCriticalSampleIndexedMoments.moment

theorem linear_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (BoundedCriticalSampleIndexedProbe.linear P T (BoundedCriticalSampleIndexedProbeFrame.row P c h d i j) : ℚ) =
      BoundedCriticalSampleBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : BoundedCriticalSampleIndexedProbe.linearQuery (BoundedCriticalSampleIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedCriticalSampleIndexedProbe.linearQuery, BoundedCriticalSampleIndexedProbeFrame.row,
      BoundedCriticalSampleIndexedProbeFrame.context, BoundedCriticalSampleProbeEntries.hashContext,
      BoundedCriticalSampleProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, BoundedCriticalSampleIndexedProbeFrame.hash_original]
  rw [BoundedCriticalSampleIndexedProbe.linear, hq, BoundedCriticalSampleIndexedMoments.moment_packet]
  unfold BoundedCriticalSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((BoundedCriticalSampleIndexedProbe.matrix P T (BoundedCriticalSampleIndexedProbeFrame.context P c h d)).submatrix
      (BoundedCriticalSampleIndexedProbeFrame.indexEquiv P c h d) (BoundedCriticalSampleIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedCriticalSamplePointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedCriticalSampleIndexedProbe.matrix, BoundedCriticalSampleIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedCriticalSampleProbeEntries.constant P (BoundedCriticalSampleIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (BoundedCriticalSampleIndexedProbe.linear P T (BoundedCriticalSampleIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [BoundedCriticalSampleIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (BoundedCriticalSampleIndexedProbe.matrix P T (BoundedCriticalSampleIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (BoundedCriticalSamplePointProbe.matrix P c (feature P T c d) h).det := by
  let A := BoundedCriticalSampleIndexedProbe.matrix P T (BoundedCriticalSampleIndexedProbeFrame.context P c h d)
  let e := BoundedCriticalSampleIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (BoundedCriticalSampleIndexedProbe.firstCoefficient P T (BoundedCriticalSampleIndexedProbeFrame.context P c h d)) =
      SignType.sign ((BoundedCriticalSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (BoundedCriticalSampleIndexedProbe.firstCoefficient P T (BoundedCriticalSampleIndexedProbeFrame.context P c h d) : ℚ) =
      (BoundedCriticalSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold BoundedCriticalSampleIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Readers) (T : Test) (c d : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    SignType.sign (BoundedCriticalSampleIndexedProbe.firstCoefficient P T
        (BoundedCriticalSampleIndexedProbeFrame.context P c (BoundedCriticalSampleHashChoice.hash P c x) d)) *
      SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P unit
        (BoundedCriticalSampleProbeSource.context P c (BoundedCriticalSampleHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : BoundedCriticalSampleTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [BoundedCriticalSampleTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, BoundedCriticalSampleTestProbeSource.sign_packet, hu]
  have H := BoundedCriticalSamplePointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeSource
