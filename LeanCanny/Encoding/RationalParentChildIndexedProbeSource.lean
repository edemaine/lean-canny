/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildIndexedProbe
public import LeanCanny.Encoding.RationalParentChildIndexedProbeFrame
public import LeanCanny.Encoding.RationalParentChildTestProbeSource

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildIndexedProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildTestMoments
open RationalParentChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

noncomputable def feature (P : Inputs) (T : Test) (c d : List Bool) : RationalParentChildRecordSpan.Root P c → ℚ :=
  fun x => sign T (pair c d) x.val

attribute [local irreducible] RationalParentChildIndexedProbe.linear RationalParentChildIndexedMoments.moment

theorem linear_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool)
    (i j : Fin (RationalParentChildRegularCount.count P c)) :
    (RationalParentChildIndexedProbe.linear P T (RationalParentChildIndexedProbeFrame.row P c h d i j) : ℚ) =
      RationalParentChildBasisPencil.weighted P c (feature P T c d) i j := by
  have hq : RationalParentChildIndexedProbe.linearQuery (RationalParentChildIndexedProbeFrame.row P c h d i j) =
      pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [RationalParentChildIndexedProbe.linearQuery, RationalParentChildIndexedProbeFrame.row,
      RationalParentChildIndexedProbeFrame.context, RationalParentChildProbeEntries.hashContext,
      RationalParentChildProbeEntries.featureCode,
      pairFst_pair, pairSnd_pair, RationalParentChildIndexedProbeFrame.hash_original]
  rw [RationalParentChildIndexedProbe.linear, hq, RationalParentChildIndexedMoments.moment_packet]
  unfold RationalParentChildBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    ((RationalParentChildIndexedProbe.matrix P T (RationalParentChildIndexedProbeFrame.context P c h d)).submatrix
      (RationalParentChildIndexedProbeFrame.indexEquiv P c h d) (RationalParentChildIndexedProbeFrame.indexEquiv P c h d)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = RationalParentChildPointProbe.matrix P c (feature P T c d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, RationalParentChildIndexedProbe.matrix, RationalParentChildIndexedProbeFrame.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (RationalParentChildProbeEntries.constant P (RationalParentChildIndexedProbeFrame.row P c h d i j) : ℚ) +
    C (RationalParentChildIndexedProbe.linear P T (RationalParentChildIndexedProbeFrame.row P c h d i j) : ℚ) * X = _
  rw [RationalParentChildIndexedProbeFrame.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    (RationalParentChildIndexedProbe.matrix P T (RationalParentChildIndexedProbeFrame.context P c h d)).det.map (Int.castRingHom ℚ) =
      (RationalParentChildPointProbe.matrix P c (feature P T c d) h).det := by
  let A := RationalParentChildIndexedProbe.matrix P T (RationalParentChildIndexedProbeFrame.context P c h d)
  let e := RationalParentChildIndexedProbeFrame.indexEquiv P c h d
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P T c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Inputs) (T : Test) (c : List Bool) (h : ℤ) (d : List Bool) :
    SignType.sign (RationalParentChildIndexedProbe.firstCoefficient P T (RationalParentChildIndexedProbeFrame.context P c h d)) =
      SignType.sign ((RationalParentChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P T c h d)
  have hc : (RationalParentChildIndexedProbe.firstCoefficient P T (RationalParentChildIndexedProbeFrame.context P c h d) : ℚ) =
      (RationalParentChildPointProbe.matrix P c (feature P T c d) h).det.coeff 1 := by
    unfold RationalParentChildIndexedProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Inputs) (T : Test) (c d : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    SignType.sign (RationalParentChildIndexedProbe.firstCoefficient P T
        (RationalParentChildIndexedProbeFrame.context P c (RationalParentChildHashChoice.hash P c x) d)) *
      SignType.sign (RationalParentChildTestProbe.firstCoefficient P unit
        (RationalParentChildProbeSource.context P c (RationalParentChildHashChoice.hash P c x) 0)) =
          sign T (pair c d) x.val := by
  have hu : RationalParentChildTestProbeSource.feature P unit c = fun _ => 1 := by
    funext y
    simp only [RationalParentChildTestProbeSource.feature, sign_unit]
    rfl
  rw [sign_packet, RationalParentChildTestProbeSource.sign_packet, hu]
  have H := RationalParentChildPointProbe.sign_at_root P c (feature P T c d) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.RationalParentChildIndexedProbeSource
