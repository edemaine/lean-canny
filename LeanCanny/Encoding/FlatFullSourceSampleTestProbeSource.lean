/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open FlatFullSourceSampleTestMoments
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c : List Bool) : FlatFullSourceSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] FlatFullSourceSampleTestProbe.linear FlatFullSourceSampleTestMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (FlatFullSourceSampleTestProbe.linear P T (FlatFullSourceSampleProbeSource.row P c h 0 i j) : ℚ) =
      FlatFullSourceSampleBasisPencil.weighted P c (feature P T c) i j := by
  have hq : FlatFullSourceSampleTestProbe.linearQuery (FlatFullSourceSampleProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [FlatFullSourceSampleTestProbe.linearQuery, FlatFullSourceSampleProbeSource.row,
      FlatFullSourceSampleProbeSource.context, FlatFullSourceSampleProbeEntries.context, FlatFullSourceSampleProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, FlatFullSourceSampleProbeSource.hash_original]
  rw [FlatFullSourceSampleTestProbe.linear, hq, moment_packet]
  unfold FlatFullSourceSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    ((FlatFullSourceSampleTestProbe.matrix P T (FlatFullSourceSampleProbeSource.context P c h 0)).submatrix
      (FlatFullSourceSampleProbeSource.indexEquiv P c h 0) (FlatFullSourceSampleProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = FlatFullSourceSamplePointProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, FlatFullSourceSampleTestProbe.matrix, FlatFullSourceSampleProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (FlatFullSourceSampleProbeEntries.constant P (FlatFullSourceSampleProbeSource.row P c h 0 i j) : ℚ) +
    C (FlatFullSourceSampleTestProbe.linear P T (FlatFullSourceSampleProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [FlatFullSourceSampleProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    (FlatFullSourceSampleTestProbe.matrix P T (FlatFullSourceSampleProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (FlatFullSourceSamplePointProbe.matrix P c (feature P T c) h).det := by
  let A := FlatFullSourceSampleTestProbe.matrix P T (FlatFullSourceSampleProbeSource.context P c h 0)
  let e := FlatFullSourceSampleProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (FlatFullSourceSampleTestProbe.firstCoefficient P T (FlatFullSourceSampleProbeSource.context P c h 0)) =
      SignType.sign ((FlatFullSourceSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (FlatFullSourceSampleTestProbe.firstCoefficient P T (FlatFullSourceSampleProbeSource.context P c h 0) : ℚ) =
      (FlatFullSourceSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold FlatFullSourceSampleTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c : List Bool) (x : FlatFullSourceSampleRecordSpan.Root P c) :
    SignType.sign (FlatFullSourceSampleTestProbe.firstCoefficient P T
        (FlatFullSourceSampleProbeSource.context P c (FlatFullSourceSampleHashChoice.hash P c x) 0)) *
      SignType.sign (FlatFullSourceSampleTestProbe.firstCoefficient P unit
        (FlatFullSourceSampleProbeSource.context P c (FlatFullSourceSampleHashChoice.hash P c x) 0)) = sign T c x.val := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  rw [sign_packet, sign_packet, hu]
  have H := FlatFullSourceSamplePointProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

theorem unit_nonzero (P : Inputs) (c : List Bool) (x : FlatFullSourceSampleRecordSpan.Root P c) :
    FlatFullSourceSampleTestProbe.firstCoefficient P unit
      (FlatFullSourceSampleProbeSource.context P c (FlatFullSourceSampleHashChoice.hash P c x) 0) ≠ 0 := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  have H := congrArg (fun p : ℚ[X] => p.coeff 1)
    (determinant_packet P unit c (FlatFullSourceSampleHashChoice.hash P c x))
  have hc : (FlatFullSourceSampleTestProbe.firstCoefficient P unit
      (FlatFullSourceSampleProbeSource.context P c (FlatFullSourceSampleHashChoice.hash P c x) 0) : ℚ) =
      (FlatFullSourceSamplePointProbe.matrix P c (fun _ => 1) (FlatFullSourceSampleHashChoice.hash P c x)).det.coeff 1 := by
    simpa only [FlatFullSourceSampleTestProbe.firstCoefficient, Polynomial.coeff_map,
      Int.coe_castRingHom, hu] using H
  intro hz
  apply FlatFullSourceSamplePointProbe.denominator_nonzero P c x
  rw [← hc, hz, Int.cast_zero]

end LeanCanny.Encoding.FlatFullSourceSampleTestProbeSource
