/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleTestMoments
open scoped Classical BigOperators

noncomputable def feature (P : Readers) (T : Test) (c : List Bool) : BoundedCriticalSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] BoundedCriticalSampleTestProbe.linear BoundedCriticalSampleTestMoments.moment

theorem linear_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (BoundedCriticalSampleTestProbe.linear P T (BoundedCriticalSampleProbeSource.row P c h 0 i j) : ℚ) =
      BoundedCriticalSampleBasisPencil.weighted P c (feature P T c) i j := by
  have hq : BoundedCriticalSampleTestProbe.linearQuery (BoundedCriticalSampleProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedCriticalSampleTestProbe.linearQuery, BoundedCriticalSampleProbeSource.row,
      BoundedCriticalSampleProbeSource.context, BoundedCriticalSampleProbeEntries.context, BoundedCriticalSampleProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, BoundedCriticalSampleProbeSource.hash_original]
  rw [BoundedCriticalSampleTestProbe.linear, hq, moment_packet]
  unfold BoundedCriticalSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    ((BoundedCriticalSampleTestProbe.matrix P T (BoundedCriticalSampleProbeSource.context P c h 0)).submatrix
      (BoundedCriticalSampleProbeSource.indexEquiv P c h 0) (BoundedCriticalSampleProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedCriticalSamplePointProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedCriticalSampleTestProbe.matrix, BoundedCriticalSampleProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedCriticalSampleProbeEntries.constant P (BoundedCriticalSampleProbeSource.row P c h 0 i j) : ℚ) +
    C (BoundedCriticalSampleTestProbe.linear P T (BoundedCriticalSampleProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [BoundedCriticalSampleProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    (BoundedCriticalSampleTestProbe.matrix P T (BoundedCriticalSampleProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (BoundedCriticalSamplePointProbe.matrix P c (feature P T c) h).det := by
  let A := BoundedCriticalSampleTestProbe.matrix P T (BoundedCriticalSampleProbeSource.context P c h 0)
  let e := BoundedCriticalSampleProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Readers) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P T (BoundedCriticalSampleProbeSource.context P c h 0)) =
      SignType.sign ((BoundedCriticalSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (BoundedCriticalSampleTestProbe.firstCoefficient P T (BoundedCriticalSampleProbeSource.context P c h 0) : ℚ) =
      (BoundedCriticalSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold BoundedCriticalSampleTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Readers) (T : Test) (c : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P T
        (BoundedCriticalSampleProbeSource.context P c (BoundedCriticalSampleHashChoice.hash P c x) 0)) *
      SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P unit
        (BoundedCriticalSampleProbeSource.context P c (BoundedCriticalSampleHashChoice.hash P c x) 0)) = sign T c x.val := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  rw [sign_packet, sign_packet, hu]
  have H := BoundedCriticalSamplePointProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

theorem unit_nonzero (P : Readers) (c : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    BoundedCriticalSampleTestProbe.firstCoefficient P unit
      (BoundedCriticalSampleProbeSource.context P c (BoundedCriticalSampleHashChoice.hash P c x) 0) ≠ 0 := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  have H := congrArg (fun p : ℚ[X] => p.coeff 1)
    (determinant_packet P unit c (BoundedCriticalSampleHashChoice.hash P c x))
  have hc : (BoundedCriticalSampleTestProbe.firstCoefficient P unit
      (BoundedCriticalSampleProbeSource.context P c (BoundedCriticalSampleHashChoice.hash P c x) 0) : ℚ) =
      (BoundedCriticalSamplePointProbe.matrix P c (fun _ => 1) (BoundedCriticalSampleHashChoice.hash P c x)).det.coeff 1 := by
    simpa only [BoundedCriticalSampleTestProbe.firstCoefficient, Polynomial.coeff_map,
      Int.coe_castRingHom, hu] using H
  intro hz
  apply BoundedCriticalSamplePointProbe.denominator_nonzero P c x
  rw [← hc, hz, Int.cast_zero]

end LeanCanny.Encoding.BoundedCriticalSampleTestProbeSource
