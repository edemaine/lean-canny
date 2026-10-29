/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildTestMoments
open RationalParentChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c : List Bool) : RationalParentChildRecordSpan.Root P c → ℚ :=
  fun x => sign T c x.val

attribute [local irreducible] RationalParentChildTestProbe.linear RationalParentChildTestMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ)
    (i j : Fin (RationalParentChildRegularCount.count P c)) :
    (RationalParentChildTestProbe.linear P T (RationalParentChildProbeSource.row P c h 0 i j) : ℚ) =
      RationalParentChildBasisPencil.weighted P c (feature P T c) i j := by
  have hq : RationalParentChildTestProbe.linearQuery (RationalParentChildProbeSource.row P c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [RationalParentChildTestProbe.linearQuery, RationalParentChildProbeSource.row,
      RationalParentChildProbeSource.context, RationalParentChildProbeEntries.context, RationalParentChildProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, RationalParentChildProbeSource.hash_original]
  rw [RationalParentChildTestProbe.linear, hq, moment_packet]
  unfold RationalParentChildBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    ((RationalParentChildTestProbe.matrix P T (RationalParentChildProbeSource.context P c h 0)).submatrix
      (RationalParentChildProbeSource.indexEquiv P c h 0) (RationalParentChildProbeSource.indexEquiv P c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = RationalParentChildPointProbe.matrix P c (feature P T c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, RationalParentChildTestProbe.matrix, RationalParentChildProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (RationalParentChildProbeEntries.constant P (RationalParentChildProbeSource.row P c h 0 i j) : ℚ) +
    C (RationalParentChildTestProbe.linear P T (RationalParentChildProbeSource.row P c h 0 i j) : ℚ) * X = _
  rw [RationalParentChildProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    (RationalParentChildTestProbe.matrix P T (RationalParentChildProbeSource.context P c h 0)).det.map (Int.castRingHom ℚ) =
      (RationalParentChildPointProbe.matrix P c (feature P T c) h).det := by
  let A := RationalParentChildTestProbe.matrix P T (RationalParentChildProbeSource.context P c h 0)
  let e := RationalParentChildProbeSource.indexEquiv P c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) :
    SignType.sign (RationalParentChildTestProbe.firstCoefficient P T (RationalParentChildProbeSource.context P c h 0)) =
      SignType.sign ((RationalParentChildPointProbe.matrix P c (feature P T c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h)
  have hc : (RationalParentChildTestProbe.firstCoefficient P T (RationalParentChildProbeSource.context P c h 0) : ℚ) =
      (RationalParentChildPointProbe.matrix P c (feature P T c) h).det.coeff 1 := by
    unfold RationalParentChildTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    SignType.sign (RationalParentChildTestProbe.firstCoefficient P T
        (RationalParentChildProbeSource.context P c (RationalParentChildHashChoice.hash P c x) 0)) *
      SignType.sign (RationalParentChildTestProbe.firstCoefficient P unit
        (RationalParentChildProbeSource.context P c (RationalParentChildHashChoice.hash P c x) 0)) = sign T c x.val := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  rw [sign_packet, sign_packet, hu]
  have H := RationalParentChildPointProbe.sign_at_root P c (feature P T c) x
  simpa only [feature, sign_cast] using H

theorem unit_nonzero (P : Inputs) (c : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    RationalParentChildTestProbe.firstCoefficient P unit
      (RationalParentChildProbeSource.context P c (RationalParentChildHashChoice.hash P c x) 0) ≠ 0 := by
  have hu : feature P unit c = fun _ => 1 := by
    funext y
    simp only [feature, sign_unit]
    rfl
  have H := congrArg (fun p : ℚ[X] => p.coeff 1)
    (determinant_packet P unit c (RationalParentChildHashChoice.hash P c x))
  have hc : (RationalParentChildTestProbe.firstCoefficient P unit
      (RationalParentChildProbeSource.context P c (RationalParentChildHashChoice.hash P c x) 0) : ℚ) =
      (RationalParentChildPointProbe.matrix P c (fun _ => 1) (RationalParentChildHashChoice.hash P c x)).det.coeff 1 := by
    simpa only [RationalParentChildTestProbe.firstCoefficient, Polynomial.coeff_map,
      Int.coe_castRingHom, hu] using H
  intro hz
  apply RationalParentChildPointProbe.denominator_nonzero P c x
  rw [← hc, hz, Int.cast_zero]

end LeanCanny.Encoding.RationalParentChildTestProbeSource
