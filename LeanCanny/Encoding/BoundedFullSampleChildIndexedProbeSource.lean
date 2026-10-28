/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildIndexedProbe
public import LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeFrame
public import LeanCanny.Encoding.BoundedFullSampleChildTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildTestMoments
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c d : List Bool) : BoundedFullSampleChildRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] BoundedFullSampleChildIndexedProbe.linear BoundedFullSampleChildIndexedMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (BoundedFullSampleChildIndexedProbe.linear P T (BoundedFullSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) =
      BoundedFullSampleChildBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : BoundedFullSampleChildIndexedProbe.linearQuery (BoundedFullSampleChildIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedFullSampleChildIndexedProbe.linearQuery, BoundedFullSampleChildIndexedProbeFrame.row,
      BoundedFullSampleChildIndexedProbeFrame.context, BoundedFullSampleChildProbeEntries.hashContext,
      BoundedFullSampleChildProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, BoundedFullSampleChildIndexedProbeFrame.hash_original]
  rw [BoundedFullSampleChildIndexedProbe.linear, hq, BoundedFullSampleChildIndexedMoments.moment_packet]
  unfold BoundedFullSampleChildBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((BoundedFullSampleChildIndexedProbe.matrix P T (BoundedFullSampleChildIndexedProbeFrame.context P c h d)).submatrix
      (BoundedFullSampleChildIndexedProbeFrame.indexEquiv P c h d) (BoundedFullSampleChildIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedFullSampleChildPointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedFullSampleChildIndexedProbe.matrix, BoundedFullSampleChildIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedFullSampleChildProbeEntries.constant P (BoundedFullSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (BoundedFullSampleChildIndexedProbe.linear P T (BoundedFullSampleChildIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [BoundedFullSampleChildIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (BoundedFullSampleChildIndexedProbe.matrix P T (BoundedFullSampleChildIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (BoundedFullSampleChildPointProbe.matrix P c (feature P T c d) h).det := by
  let A := BoundedFullSampleChildIndexedProbe.matrix P T (BoundedFullSampleChildIndexedProbeFrame.context P c h d)
  let e := BoundedFullSampleChildIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (BoundedFullSampleChildIndexedProbe.firstCoefficient P T (BoundedFullSampleChildIndexedProbeFrame.context P c h d)) =
      SignType.sign ((BoundedFullSampleChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (BoundedFullSampleChildIndexedProbe.firstCoefficient P T (BoundedFullSampleChildIndexedProbeFrame.context P c h d) : ℚ) =
      (BoundedFullSampleChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold BoundedFullSampleChildIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P c) :
    SignType.sign (BoundedFullSampleChildIndexedProbe.firstCoefficient P T
        (BoundedFullSampleChildIndexedProbeFrame.context P c (BoundedFullSampleChildHashChoice.hash P c x) d)) *
      SignType.sign (BoundedFullSampleChildTestProbe.firstCoefficient P unit
        (BoundedFullSampleChildProbeSource.context P c (BoundedFullSampleChildHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : BoundedFullSampleChildTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [BoundedFullSampleChildTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, BoundedFullSampleChildTestProbeSource.sign_packet, hu]
  have H := BoundedFullSampleChildPointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeSource
