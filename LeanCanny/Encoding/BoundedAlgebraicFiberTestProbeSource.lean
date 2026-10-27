/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberTestProbe

/-! # Correctness of polynomial-test probes at the selected root hashes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberTestProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicFiberTestMoments
open scoped Classical BigOperators

noncomputable def feature (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ :=
  fun x => sign P G c x.val

attribute [local irreducible] BoundedAlgebraicFiberTestProbe.linear BoundedAlgebraicFiberTestMoments.moment

theorem linear_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ)
    (i j : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    (BoundedAlgebraicFiberTestProbe.linear P F G (BoundedAlgebraicFiberProbeSource.row P F c h 0 i j) : ℚ) =
      BoundedAlgebraicFiberBasisPencil.weighted P F c (feature P F G c) i j := by
  have hq : BoundedAlgebraicFiberTestProbe.linearQuery (BoundedAlgebraicFiberProbeSource.row P F c h 0 i j) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    simp only [BoundedAlgebraicFiberTestProbe.linearQuery, BoundedAlgebraicFiberProbeSource.row,
      BoundedAlgebraicFiberProbeSource.context, BoundedAlgebraicFiberProbeEntries.context, BoundedAlgebraicFiberProbeEntries.hashContext,
      pairFst_pair, pairSnd_pair, BoundedAlgebraicFiberProbeSource.hash_original]
  rw [BoundedAlgebraicFiberTestProbe.linear, hq, moment_packet]
  unfold BoundedAlgebraicFiberBasisPencil.weighted feature
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem matrix_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) :
    ((BoundedAlgebraicFiberTestProbe.matrix P F G (BoundedAlgebraicFiberProbeSource.context P F c h 0)).submatrix
      (BoundedAlgebraicFiberProbeSource.indexEquiv P F c h 0) (BoundedAlgebraicFiberProbeSource.indexEquiv P F c h 0)).map
        (Polynomial.mapRingHom (Int.castRingHom ℚ)) = BoundedAlgebraicFiberSignatureProbe.matrix P F c (feature P F G c) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedAlgebraicFiberTestProbe.matrix, BoundedAlgebraicFiberProbeSource.indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedAlgebraicFiberProbeEntries.constant P F (BoundedAlgebraicFiberProbeSource.row P F c h 0 i j) : ℚ) +
    C (BoundedAlgebraicFiberTestProbe.linear P F G (BoundedAlgebraicFiberProbeSource.row P F c h 0 i j) : ℚ) * X = _
  rw [BoundedAlgebraicFiberProbeSource.constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) :
    (BoundedAlgebraicFiberTestProbe.matrix P F G (BoundedAlgebraicFiberProbeSource.context P F c h 0)).det.map (Int.castRingHom ℚ) =
      (BoundedAlgebraicFiberSignatureProbe.matrix P F c (feature P F G c) h).det := by
  let A := BoundedAlgebraicFiberTestProbe.matrix P F G (BoundedAlgebraicFiberProbeSource.context P F c h 0)
  let e := BoundedAlgebraicFiberProbeSource.indexEquiv P F c h 0
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P F G c h)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem sign_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) :
    SignType.sign (BoundedAlgebraicFiberTestProbe.firstCoefficient P F G (BoundedAlgebraicFiberProbeSource.context P F c h 0)) =
      SignType.sign ((BoundedAlgebraicFiberSignatureProbe.matrix P F c (feature P F G c) h).det.coeff 1) := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P F G c h)
  have hc : (BoundedAlgebraicFiberTestProbe.firstCoefficient P F G (BoundedAlgebraicFiberProbeSource.context P F c h 0) : ℚ) =
      (BoundedAlgebraicFiberSignatureProbe.matrix P F c (feature P F G c) h).det.coeff 1 := by
    unfold BoundedAlgebraicFiberTestProbe.firstCoefficient
    simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H
  rw [← hc]
  exact (sign_intCast _).symm

private theorem sign_cast (s : SignType) : SignType.sign (s : ℚ) = s := by cases s <;> decide

theorem pointwise (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (x : BoundedAlgebraicFiberRecordSpan.Root P F c) :
    SignType.sign (BoundedAlgebraicFiberTestProbe.firstCoefficient P F G
        (BoundedAlgebraicFiberProbeSource.context P F c (BoundedAlgebraicFiberHashChoice.hash P F c x) 0)) *
      SignType.sign (BoundedAlgebraicFiberProbeCoefficient.firstCoefficient P F true
        (BoundedAlgebraicFiberProbeSource.context P F c (BoundedAlgebraicFiberHashChoice.hash P F c x) 0)) = sign P G c x.val := by
  rw [sign_packet, BoundedAlgebraicFiberProbeSource.sign_packet P F true c _ ⟨0, Nat.succ_pos _⟩]
  simp only [BoundedAlgebraicFiberProbeSource.featureFunction, ↓reduceIte]
  have H := BoundedAlgebraicFiberSignatureProbe.sign_at_root P F c (feature P F G c) x
  simpa only [feature, sign_cast] using H

end LeanCanny.Encoding.BoundedAlgebraicFiberTestProbeSource
