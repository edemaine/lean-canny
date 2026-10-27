/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberProbeCoefficient
public import LeanCanny.Encoding.BoundedCriticalSampleFiberSignatureProbe

/-! # Correctness of native signature-probe determinant coefficients

For the internally selected hash context, the integer matrix maps to the
proved rational signature probe. Casting its indices changes no determinant.
Both numerator and denominator first coefficients therefore have the exact
signs used by the pointwise recovery identity.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical BigOperators

noncomputable def context (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  BoundedCriticalSampleFiberProbeEntries.context (BoundedCriticalSampleFiberHashChoice.value P F c) h d

theorem hash_original (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    BoundedCriticalSampleFiberWeightedMoments.original (BoundedCriticalSampleFiberHashChoice.value P F c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleFiberHashChoice.value_spec P F c
  rw [hv]
  simp only [BoundedCriticalSampleFiberWeightedMoments.original, BoundedCriticalSampleFiberWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) :
    BoundedCriticalSampleFiberProbeEntries.dimension (context P F c h d) = BoundedCriticalSampleSlice.RootCount.count P F c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleFiberHashChoice.value_spec P F c
  simp only [BoundedCriticalSampleFiberProbeEntries.dimension, context, BoundedCriticalSampleFiberProbeEntries.context,
    BoundedCriticalSampleFiberProbeEntries.hashContext, pairFst_pair]
  rw [hv, BoundedCriticalSampleFiberPencilSource.dimension_context]

noncomputable def indexEquiv (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (BoundedCriticalSampleSlice.RootCount.count P F c) ≃ Fin (BoundedCriticalSampleFiberProbeEntries.dimension (context P F c h d)) :=
  finCongr (dimension_context P F c h d).symm
theorem indexEquiv_val (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) : (indexEquiv P F c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) : List Bool :=
  pair (context P F c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    BoundedCriticalSampleFiberProbeEntries.entryQuery (row P F c h d i j) = pair (BoundedCriticalSampleFiberHashChoice.value P F c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [BoundedCriticalSampleFiberProbeEntries.entryQuery, row, context, BoundedCriticalSampleFiberProbeEntries.context,
    BoundedCriticalSampleFiberProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] BoundedCriticalSampleFiberProbeEntries.gram BoundedCriticalSampleFiberProbeEntries.weighted
  BoundedCriticalSampleFiberProbeEntries.constant BoundedCriticalSampleFiberProbeEntries.linear
  BoundedCriticalSampleFiberWeightedMoments.entry BoundedCriticalSampleFiberFeatureMoments.moment

theorem gram_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    (BoundedCriticalSampleFiberProbeEntries.gram P F (row P F c h d i j) : ℚ) = BoundedCriticalSampleFiberBasisGram.gram P F c i j := by
  have hq : BoundedCriticalSampleFiberPencilEntries.gramQuery (BoundedCriticalSampleFiberProbeEntries.entryQuery (row P F c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [BoundedCriticalSampleFiberPencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [BoundedCriticalSampleFiberProbeEntries.gram, BoundedCriticalSampleFiberPencilEntries.gram, hq]
  exact BoundedCriticalSampleFiberBasisGram.entry_packet P F c i j

theorem weighted_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    (BoundedCriticalSampleFiberProbeEntries.weighted P F (row P F c h d i j) : ℚ) =
      BoundedCriticalSampleFiberBasisPencil.weighted P F c (BoundedCriticalSampleFiberSignatureProbe.hashFunction P F c) i j := by
  rw [BoundedCriticalSampleFiberProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedCriticalSampleFiberHashChoice.value_spec P F c
  have hh : BoundedCriticalSampleFiberSignatureProbe.hashFunction P F c =
      fun x => (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold BoundedCriticalSampleFiberSignatureProbe.hashFunction BoundedCriticalSampleFiberHashChoice.hash
    rw [hv]
    simp only [BoundedCriticalSampleFiberWeightedMoments.context, BoundedCriticalSampleFiberWeightedMoments.modulus,
      BoundedCriticalSampleFiberWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact BoundedCriticalSampleFiberWeightedMoments.entry_packet P F c m t i j

theorem constant_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    (BoundedCriticalSampleFiberProbeEntries.constant P F (row P F c h d i j) : ℚ) =
      (h : ℚ) * BoundedCriticalSampleFiberBasisGram.gram P F c i j -
        BoundedCriticalSampleFiberBasisPencil.weighted P F c (BoundedCriticalSampleFiberSignatureProbe.hashFunction P F c) i j := by
  have hp : BoundedCriticalSampleFiberProbeEntries.pointValue (pairFst (row P F c h d i j)) = h := by
    simp only [row, pairFst_pair, context, BoundedCriticalSampleFiberProbeEntries.pointValue_packet]
  rw [BoundedCriticalSampleFiberProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

noncomputable def featureFunction (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (unit : Bool) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    BoundedCriticalSampleFiberRecordSpan.Root P F c → ℚ := if unit then fun _ => 1 else fun x => BoundedCriticalSampleFiberThom.signature P F c x d

theorem unit_weighted (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : BoundedCriticalSampleFiberBasisPencil.weighted P F c (fun _ => 1) =
    BoundedCriticalSampleFiberBasisGram.gram P F c := by
  apply Matrix.ext
  intro i j
  simp only [BoundedCriticalSampleFiberBasisPencil.weighted, BoundedCriticalSampleFiberBasisGram.gram,
    BoundedCriticalSampleFiberBasisGram.matrix, mul_one]
  change _ = ∑ x, _
  rfl

theorem linear_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (c : List Bool) (h : ℤ)
    (d : BoundedCriticalSampleFiberThom.Feature F c) (i j : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    (BoundedCriticalSampleFiberProbeEntries.linear P F unit (row P F c h d.val i j) : ℚ) =
      BoundedCriticalSampleFiberBasisPencil.weighted P F c (featureFunction P F c unit d) i j := by
  cases unit with
  | true =>
    unfold BoundedCriticalSampleFiberProbeEntries.linear featureFunction
    change (BoundedCriticalSampleFiberProbeEntries.gram P F (row P F c h d.val i j) : ℚ) =
      BoundedCriticalSampleFiberBasisPencil.weighted P F c (fun _ => 1) i j
    rw [gram_packet, unit_weighted]
  | false =>
    have hq : BoundedCriticalSampleFiberProbeEntries.featureQuery (row P F c h d.val i j) =
        pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val))) := by
      simp only [BoundedCriticalSampleFiberProbeEntries.featureQuery, row, context, BoundedCriticalSampleFiberProbeEntries.context,
        BoundedCriticalSampleFiberProbeEntries.hashContext, BoundedCriticalSampleFiberProbeEntries.featureCode, pairFst_pair, pairSnd_pair, hash_original]
    unfold BoundedCriticalSampleFiberProbeEntries.linear featureFunction
    change (BoundedCriticalSampleFiberFeatureMoments.moment P F (BoundedCriticalSampleFiberProbeEntries.featureQuery (row P F c h d.val i j)) : ℚ) = _
    rw [hq, BoundedCriticalSampleFiberFeatureMoments.moment_packet]
    unfold BoundedCriticalSampleFiberBasisPencil.weighted
    apply Finset.sum_congr rfl
    intro x _
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring

theorem matrix_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    ((BoundedCriticalSampleFiberProbeEntries.matrix P F unit (context P F c h d.val)).submatrix
      (indexEquiv P F c h d.val) (indexEquiv P F c h d.val)).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
        BoundedCriticalSampleFiberSignatureProbe.matrix P F c (featureFunction P F c unit d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedCriticalSampleFiberProbeEntries.matrix, indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedCriticalSampleFiberProbeEntries.constant P F (row P F c h d.val i j) : ℚ) +
    C (BoundedCriticalSampleFiberProbeEntries.linear P F unit (row P F c h d.val i j) : ℚ) * X = _
  rw [constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    (BoundedCriticalSampleFiberProbeEntries.matrix P F unit (context P F c h d.val)).det.map (Int.castRingHom ℚ) =
      (BoundedCriticalSampleFiberSignatureProbe.matrix P F c (featureFunction P F c unit d) h).det := by
  let A := BoundedCriticalSampleFiberProbeEntries.matrix P F unit (context P F c h d.val)
  let e := indexEquiv P F c h d.val
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P F unit c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem coefficient_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    (BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient P F unit (context P F c h d.val) : ℚ) =
      (BoundedCriticalSampleFiberSignatureProbe.matrix P F c (featureFunction P F c unit d) h).det.coeff 1 := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P F unit c h d)
  unfold BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H

theorem sign_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    SignType.sign (BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient P F unit (context P F c h d.val)) =
      SignType.sign ((BoundedCriticalSampleFiberSignatureProbe.matrix P F c (featureFunction P F c unit d) h).det.coeff 1) := by
  rw [← coefficient_packet]
  exact (sign_intCast _).symm

end LeanCanny.Encoding.BoundedCriticalSampleFiberProbeSource
