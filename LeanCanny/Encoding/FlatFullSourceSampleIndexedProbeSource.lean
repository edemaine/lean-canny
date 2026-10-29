/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleIndexedProbe
public import LeanCanny.Encoding.FlatFullSourceSampleIndexedProbeFrame
public import LeanCanny.Encoding.FlatFullSourceSampleTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open FlatFullSourceSampleTestMoments
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c d : List Bool) : FlatFullSourceSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] FlatFullSourceSampleIndexedProbe.linear FlatFullSourceSampleIndexedMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (FlatFullSourceSampleIndexedProbe.linear P T (FlatFullSourceSampleIndexedProbeFrame.row P c h d i j) : ℚ) =
      FlatFullSourceSampleBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : FlatFullSourceSampleIndexedProbe.linearQuery (FlatFullSourceSampleIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [FlatFullSourceSampleIndexedProbe.linearQuery, FlatFullSourceSampleIndexedProbeFrame.row,
      FlatFullSourceSampleIndexedProbeFrame.context, FlatFullSourceSampleProbeEntries.hashContext,
      FlatFullSourceSampleProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, FlatFullSourceSampleIndexedProbeFrame.hash_original]
  rw [FlatFullSourceSampleIndexedProbe.linear, hq, FlatFullSourceSampleIndexedMoments.moment_packet]
  unfold FlatFullSourceSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((FlatFullSourceSampleIndexedProbe.matrix P T (FlatFullSourceSampleIndexedProbeFrame.context P c h d)).submatrix
      (FlatFullSourceSampleIndexedProbeFrame.indexEquiv P c h d) (FlatFullSourceSampleIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = FlatFullSourceSamplePointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, FlatFullSourceSampleIndexedProbe.matrix, FlatFullSourceSampleIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (FlatFullSourceSampleProbeEntries.constant P (FlatFullSourceSampleIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (FlatFullSourceSampleIndexedProbe.linear P T (FlatFullSourceSampleIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [FlatFullSourceSampleIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (FlatFullSourceSampleIndexedProbe.matrix P T (FlatFullSourceSampleIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (FlatFullSourceSamplePointProbe.matrix P c (feature P T c d) h).det := by
  let A := FlatFullSourceSampleIndexedProbe.matrix P T (FlatFullSourceSampleIndexedProbeFrame.context P c h d)
  let e := FlatFullSourceSampleIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (FlatFullSourceSampleIndexedProbe.firstCoefficient P T (FlatFullSourceSampleIndexedProbeFrame.context P c h d)) =
      SignType.sign ((FlatFullSourceSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (FlatFullSourceSampleIndexedProbe.firstCoefficient P T (FlatFullSourceSampleIndexedProbeFrame.context P c h d) : ℚ) =
      (FlatFullSourceSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold FlatFullSourceSampleIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c d : List Bool) (x : FlatFullSourceSampleRecordSpan.Root P c) :
    SignType.sign (FlatFullSourceSampleIndexedProbe.firstCoefficient P T
        (FlatFullSourceSampleIndexedProbeFrame.context P c (FlatFullSourceSampleHashChoice.hash P c x) d)) *
      SignType.sign (FlatFullSourceSampleTestProbe.firstCoefficient P unit
        (FlatFullSourceSampleProbeSource.context P c (FlatFullSourceSampleHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : FlatFullSourceSampleTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [FlatFullSourceSampleTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, FlatFullSourceSampleTestProbeSource.sign_packet, hu]
  have H := FlatFullSourceSamplePointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.FlatFullSourceSampleIndexedProbeSource
