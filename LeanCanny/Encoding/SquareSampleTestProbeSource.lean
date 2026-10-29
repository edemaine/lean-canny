/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSampleTestMoments
open SquareSampleInput (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c : List Bool) : SquareSampleRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] SquareSampleTestProbe.linear SquareSampleTestMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (SquareSampleRegularCount.count P c)) :
    (SquareSampleTestProbe.linear P T (SquareSampleProbeSource.row P c h 0 i j) : ℚ) =
      SquareSampleBasisPencil.weighted P c (feature P T c) i j := by
  have hq : SquareSampleTestProbe.linearQuery (SquareSampleProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [SquareSampleTestProbe.linearQuery, SquareSampleProbeSource.row,
      SquareSampleProbeSource.context, SquareSampleProbeEntries.context, SquareSampleProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, SquareSampleProbeSource.hash_original]
  rw [SquareSampleTestProbe.linear, hq, moment_packet]
  unfold SquareSampleBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    ((SquareSampleTestProbe.matrix P T (SquareSampleProbeSource.context P c h 0)).submatrix
      (SquareSampleProbeSource.indexEquiv P c h 0) (SquareSampleProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = SquareSamplePointProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, SquareSampleTestProbe.matrix, SquareSampleProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (SquareSampleProbeEntries.constant P (SquareSampleProbeSource.row P c h 0 i j) : ℚ) +
    C (SquareSampleTestProbe.linear P T (SquareSampleProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [SquareSampleProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    (SquareSampleTestProbe.matrix P T (SquareSampleProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (SquareSamplePointProbe.matrix P c (feature P T c) h).det := by
  let A := SquareSampleTestProbe.matrix P T (SquareSampleProbeSource.context P c h 0)
  let e := SquareSampleProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (SquareSampleTestProbe.firstCoefficient P T (SquareSampleProbeSource.context P c h 0)) =
      SignType.sign ((SquareSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (SquareSampleTestProbe.firstCoefficient P T (SquareSampleProbeSource.context P c h 0) : ℚ) =
      (SquareSamplePointProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold SquareSampleTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    SignType.sign (SquareSampleTestProbe.firstCoefficient P T
        (SquareSampleProbeSource.context P c (SquareSampleHashChoice.hash P c x) 0)) *
      SignType.sign (SquareSampleTestProbe.firstCoefficient P unit
        (SquareSampleProbeSource.context P c (SquareSampleHashChoice.hash P c x) 0)) = sign T c x.val := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  rw [sign_packet, sign_packet, hu]
  have H := SquareSamplePointProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

theorem unit_nonzero (P : Inputs) (c : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    SquareSampleTestProbe.firstCoefficient P unit
      (SquareSampleProbeSource.context P c (SquareSampleHashChoice.hash P c x) 0) ≠ 0 := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  have H := congrArg (fun p : ℚ[X] => p.coeff 1)
    (determinant_packet P unit c (SquareSampleHashChoice.hash P c x))
  have hc : (SquareSampleTestProbe.firstCoefficient P unit
      (SquareSampleProbeSource.context P c (SquareSampleHashChoice.hash P c x) 0) : ℚ) =
      (SquareSamplePointProbe.matrix P c (fun _ => 1) (SquareSampleHashChoice.hash P c x)).det.coeff 1 := by
    simpa only [SquareSampleTestProbe.firstCoefficient, Polynomial.coeff_map,
      Int.coe_castRingHom, hu] using H
  intro hz
  apply SquareSamplePointProbe.denominator_nonzero P c x
  rw [← hc, hz, Int.cast_zero]

end LeanCanny.Encoding.SquareSampleTestProbeSource
