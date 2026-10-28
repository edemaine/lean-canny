/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildIndexedProbe
public import LeanCanny.Encoding.BoundedCriticalSampleChildIndexedProbeFrame
public import LeanCanny.Encoding.BoundedCriticalSampleChildTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildTestMoments
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c d : List Bool) : BoundedCriticalSampleChildRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] BoundedCriticalSampleChildIndexedProbe.linear BoundedCriticalSampleChildIndexedMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (BoundedCriticalSampleChildIndexedProbe.linear P T (BoundedCriticalSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) =
      BoundedCriticalSampleChildBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : BoundedCriticalSampleChildIndexedProbe.linearQuery (BoundedCriticalSampleChildIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedCriticalSampleChildIndexedProbe.linearQuery, BoundedCriticalSampleChildIndexedProbeFrame.row,
      BoundedCriticalSampleChildIndexedProbeFrame.context, BoundedCriticalSampleChildProbeEntries.hashContext,
      BoundedCriticalSampleChildProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, BoundedCriticalSampleChildIndexedProbeFrame.hash_original]
  rw [BoundedCriticalSampleChildIndexedProbe.linear, hq, BoundedCriticalSampleChildIndexedMoments.moment_packet]
  unfold BoundedCriticalSampleChildBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((BoundedCriticalSampleChildIndexedProbe.matrix P T (BoundedCriticalSampleChildIndexedProbeFrame.context P c h d)).submatrix
      (BoundedCriticalSampleChildIndexedProbeFrame.indexEquiv P c h d) (BoundedCriticalSampleChildIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedCriticalSampleChildPointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedCriticalSampleChildIndexedProbe.matrix, BoundedCriticalSampleChildIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedCriticalSampleChildProbeEntries.constant P (BoundedCriticalSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (BoundedCriticalSampleChildIndexedProbe.linear P T (BoundedCriticalSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [BoundedCriticalSampleChildIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (BoundedCriticalSampleChildIndexedProbe.matrix P T (BoundedCriticalSampleChildIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (BoundedCriticalSampleChildPointProbe.matrix P c (feature P T c d) h).det := by
  let A := BoundedCriticalSampleChildIndexedProbe.matrix P T (BoundedCriticalSampleChildIndexedProbeFrame.context P c h d)
  let e := BoundedCriticalSampleChildIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (BoundedCriticalSampleChildIndexedProbe.firstCoefficient P T (BoundedCriticalSampleChildIndexedProbeFrame.context P c h d)) =
      SignType.sign ((BoundedCriticalSampleChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (BoundedCriticalSampleChildIndexedProbe.firstCoefficient P T (BoundedCriticalSampleChildIndexedProbeFrame.context P c h d) : ℚ) =
      (BoundedCriticalSampleChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold BoundedCriticalSampleChildIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    SignType.sign (BoundedCriticalSampleChildIndexedProbe.firstCoefficient P T
        (BoundedCriticalSampleChildIndexedProbeFrame.context P c (BoundedCriticalSampleChildHashChoice.hash P c x) d)) *
      SignType.sign (BoundedCriticalSampleChildTestProbe.firstCoefficient P unit
        (BoundedCriticalSampleChildProbeSource.context P c (BoundedCriticalSampleChildHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : BoundedCriticalSampleChildTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [BoundedCriticalSampleChildTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, BoundedCriticalSampleChildTestProbeSource.sign_packet, hu]
  have H := BoundedCriticalSampleChildPointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildIndexedProbeSource
