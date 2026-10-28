/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildTestMoments
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c : List Bool) : BoundedFullSampleChildRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] BoundedFullSampleChildTestProbe.linear BoundedFullSampleChildTestMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (BoundedFullSampleChildTestProbe.linear P T (BoundedFullSampleChildProbeSource.row P c h 0 i j) : ℚ) =
      BoundedFullSampleChildBasisPencil.weighted P c (feature P T c) i j := by
  have hq : BoundedFullSampleChildTestProbe.linearQuery (BoundedFullSampleChildProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedFullSampleChildTestProbe.linearQuery, BoundedFullSampleChildProbeSource.row,
      BoundedFullSampleChildProbeSource.context, BoundedFullSampleChildProbeEntries.context, BoundedFullSampleChildProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, BoundedFullSampleChildProbeSource.hash_original]
  rw [BoundedFullSampleChildTestProbe.linear, hq, moment_packet]
  unfold BoundedFullSampleChildBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    ((BoundedFullSampleChildTestProbe.matrix P T (BoundedFullSampleChildProbeSource.context P c h 0)).submatrix
      (BoundedFullSampleChildProbeSource.indexEquiv P c h 0) (BoundedFullSampleChildProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedFullSampleChildPointProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedFullSampleChildTestProbe.matrix, BoundedFullSampleChildProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedFullSampleChildProbeEntries.constant P (BoundedFullSampleChildProbeSource.row P c h 0 i j) : ℚ) +
    C (BoundedFullSampleChildTestProbe.linear P T (BoundedFullSampleChildProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [BoundedFullSampleChildProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    (BoundedFullSampleChildTestProbe.matrix P T (BoundedFullSampleChildProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (BoundedFullSampleChildPointProbe.matrix P c (feature P T c) h).det := by
  let A := BoundedFullSampleChildTestProbe.matrix P T (BoundedFullSampleChildProbeSource.context P c h 0)
  let e := BoundedFullSampleChildProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (BoundedFullSampleChildTestProbe.firstCoefficient P T (BoundedFullSampleChildProbeSource.context P c h 0)) =
      SignType.sign ((BoundedFullSampleChildPointProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (BoundedFullSampleChildTestProbe.firstCoefficient P T (BoundedFullSampleChildProbeSource.context P c h 0) : ℚ) =
      (BoundedFullSampleChildPointProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold BoundedFullSampleChildTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P c) :
    SignType.sign (BoundedFullSampleChildTestProbe.firstCoefficient P T
        (BoundedFullSampleChildProbeSource.context P c (BoundedFullSampleChildHashChoice.hash P c x) 0)) *
      SignType.sign (BoundedFullSampleChildTestProbe.firstCoefficient P unit
        (BoundedFullSampleChildProbeSource.context P c (BoundedFullSampleChildHashChoice.hash P c x) 0)) = sign T c x.val := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  rw [sign_packet, sign_packet, hu]
  have H := BoundedFullSampleChildPointProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

theorem unit_nonzero (P : Inputs) (c : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P c) :
    BoundedFullSampleChildTestProbe.firstCoefficient P unit
      (BoundedFullSampleChildProbeSource.context P c (BoundedFullSampleChildHashChoice.hash P c x) 0) ≠ 0 := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  have H := congrArg (fun p : ℚ[X] => p.coeff 1)
    (determinant_packet P unit c (BoundedFullSampleChildHashChoice.hash P c x))
  have hc : (BoundedFullSampleChildTestProbe.firstCoefficient P unit
      (BoundedFullSampleChildProbeSource.context P c (BoundedFullSampleChildHashChoice.hash P c x) 0) : ℚ) =
      (BoundedFullSampleChildPointProbe.matrix P c (fun _ => 1) (BoundedFullSampleChildHashChoice.hash P c x)).det.coeff 1 := by
    simpa only [BoundedFullSampleChildTestProbe.firstCoefficient, Polynomial.coeff_map,
      Int.coe_castRingHom, hu] using H
  intro hz
  apply BoundedFullSampleChildPointProbe.denominator_nonzero P c x
  rw [← hc, hz, Int.cast_zero]

end LeanCanny.Encoding.BoundedFullSampleChildTestProbeSource
