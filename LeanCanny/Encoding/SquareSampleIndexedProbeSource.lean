/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleIndexedProbe
public import LeanCanny.Encoding.SquareSampleIndexedProbeFrame
public import LeanCanny.Encoding.SquareSampleTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSampleTestMoments
open SquareSampleInput (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c d : List Bool) : SquareSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] SquareSampleIndexedProbe.linear SquareSampleIndexedMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (SquareSampleRegularCount.count P c)) :
    (SquareSampleIndexedProbe.linear P T (SquareSampleIndexedProbeFrame.row P c h d i j) : ℚ) =
      SquareSampleBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : SquareSampleIndexedProbe.linearQuery (SquareSampleIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [SquareSampleIndexedProbe.linearQuery, SquareSampleIndexedProbeFrame.row,
      SquareSampleIndexedProbeFrame.context, SquareSampleProbeEntries.hashContext,
      SquareSampleProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, SquareSampleIndexedProbeFrame.hash_original]
  rw [SquareSampleIndexedProbe.linear, hq, SquareSampleIndexedMoments.moment_packet]
  unfold SquareSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((SquareSampleIndexedProbe.matrix P T (SquareSampleIndexedProbeFrame.context P c h d)).submatrix
      (SquareSampleIndexedProbeFrame.indexEquiv P c h d) (SquareSampleIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = SquareSamplePointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, SquareSampleIndexedProbe.matrix, SquareSampleIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (SquareSampleProbeEntries.constant P (SquareSampleIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (SquareSampleIndexedProbe.linear P T (SquareSampleIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [SquareSampleIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (SquareSampleIndexedProbe.matrix P T (SquareSampleIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (SquareSamplePointProbe.matrix P c (feature P T c d) h).det := by
  let A := SquareSampleIndexedProbe.matrix P T (SquareSampleIndexedProbeFrame.context P c h d)
  let e := SquareSampleIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (SquareSampleIndexedProbe.firstCoefficient P T (SquareSampleIndexedProbeFrame.context P c h d)) =
      SignType.sign ((SquareSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (SquareSampleIndexedProbe.firstCoefficient P T (SquareSampleIndexedProbeFrame.context P c h d) : ℚ) =
      (SquareSamplePointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold SquareSampleIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c d : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    SignType.sign (SquareSampleIndexedProbe.firstCoefficient P T
        (SquareSampleIndexedProbeFrame.context P c (SquareSampleHashChoice.hash P c x) d)) *
      SignType.sign (SquareSampleTestProbe.firstCoefficient P unit
        (SquareSampleProbeSource.context P c (SquareSampleHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : SquareSampleTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [SquareSampleTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, SquareSampleTestProbeSource.sign_packet, hu]
  have H := SquareSamplePointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.SquareSampleIndexedProbeSource
