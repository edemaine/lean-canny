/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionProbeCoefficient
public import LeanCanny.Encoding.BoundedProjectionSignatureProbe

/-! # Correctness of native signature-probe determinant coefficients

For the internally selected hash context, the integer matrix maps to the
proved rational signature probe. Casting its indices changes no determinant.
Both numerator and denominator first coefficients therefore have the exact
signs used by the pointwise recovery identity.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionProbeSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical BigOperators

noncomputable def context (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  BoundedProjectionProbeEntries.context (BoundedProjectionHashChoice.value P c) h d

theorem hash_original (P : Readers) (c : List Bool) :
    BoundedProjectionWeightedMoments.original (BoundedProjectionHashChoice.value P c) = c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedProjectionHashChoice.value_spec P c
  rw [hv]
  simp only [BoundedProjectionWeightedMoments.original, BoundedProjectionWeightedMoments.context, pairFst_pair]

theorem dimension_context (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) :
    BoundedProjectionProbeEntries.dimension (context P c h d) = BoundedProjectionRootCount.count P c := by
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedProjectionHashChoice.value_spec P c
  simp only [BoundedProjectionProbeEntries.dimension, context, BoundedProjectionProbeEntries.context,
    BoundedProjectionProbeEntries.hashContext, pairFst_pair]
  rw [hv, BoundedProjectionPencilSource.dimension_context]

noncomputable def indexEquiv (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) :
    Fin (BoundedProjectionRootCount.count P c) ≃ Fin (BoundedProjectionProbeEntries.dimension (context P c h d)) :=
  finCongr (dimension_context P c h d).symm
theorem indexEquiv_val (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ)
    (i : Fin (BoundedProjectionRootCount.count P c)) : (indexEquiv P c h d i).val = i.val := by
  simp only [indexEquiv, finCongr_apply, Fin.val_cast]

noncomputable def row (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ)
    (i j : Fin (BoundedProjectionRootCount.count P c)) : List Bool :=
  pair (context P c h d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))

theorem entryQuery_row (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionProbeEntries.entryQuery (row P c h d i j) = pair (BoundedProjectionHashChoice.value P c)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
  simp only [BoundedProjectionProbeEntries.entryQuery, row, context, BoundedProjectionProbeEntries.context,
    BoundedProjectionProbeEntries.hashContext, pairFst_pair, pairSnd_pair]

attribute [local irreducible] BoundedProjectionProbeEntries.gram BoundedProjectionProbeEntries.weighted
  BoundedProjectionProbeEntries.constant BoundedProjectionProbeEntries.linear
  BoundedProjectionWeightedMoments.entry BoundedProjectionFeatureMoments.moment

theorem gram_packet (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionProbeEntries.gram P (row P c h d i j) : ℚ) = BoundedProjectionBasisGram.gram P c i j := by
  have hq : BoundedProjectionPencilEntries.gramQuery (BoundedProjectionProbeEntries.entryQuery (row P c h d i j)) =
      pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
    rw [entryQuery_row]
    simp only [BoundedProjectionPencilEntries.gramQuery, pairFst_pair, pairSnd_pair, hash_original]
  rw [BoundedProjectionProbeEntries.gram, BoundedProjectionPencilEntries.gram, hq]
  exact BoundedProjectionBasisGram.entry_packet P c i j

theorem weighted_packet (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionProbeEntries.weighted P (row P c h d i j) : ℚ) =
      BoundedProjectionBasisPencil.weighted P c (BoundedProjectionSignatureProbe.hashFunction P c) i j := by
  rw [BoundedProjectionProbeEntries.weighted, entryQuery_row]
  obtain ⟨m, t, hv, _, _, _⟩ := BoundedProjectionHashChoice.value_spec P c
  have hh : BoundedProjectionSignatureProbe.hashFunction P c =
      fun x => (BoundedProjectionRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ) := by
    funext x
    unfold BoundedProjectionSignatureProbe.hashFunction BoundedProjectionHashChoice.hash
    rw [hv]
    simp only [BoundedProjectionWeightedMoments.context, BoundedProjectionWeightedMoments.modulus,
      BoundedProjectionWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [hv, hh]
  exact BoundedProjectionWeightedMoments.entry_packet P c m t i j

theorem constant_packet (P : Readers) (c : List Bool) (h : ℤ) (d : ℕ) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionProbeEntries.constant P (row P c h d i j) : ℚ) =
      (h : ℚ) * BoundedProjectionBasisGram.gram P c i j -
        BoundedProjectionBasisPencil.weighted P c (BoundedProjectionSignatureProbe.hashFunction P c) i j := by
  have hp : BoundedProjectionProbeEntries.pointValue (pairFst (row P c h d i j)) = h := by
    simp only [row, pairFst_pair, context, BoundedProjectionProbeEntries.pointValue_packet]
  rw [BoundedProjectionProbeEntries.constant, hp, Int.cast_sub, Int.cast_mul, gram_packet, weighted_packet]

noncomputable def featureFunction (P : Readers) (c : List Bool) (unit : Bool) (d : BoundedProjectionMoments.Feature P c) :
    BoundedProjectionRecordSpan.Root P c → ℚ := if unit then fun _ => 1 else fun x => BoundedProjectionMoments.signature P c x d

theorem unit_weighted (P : Readers) (c : List Bool) : BoundedProjectionBasisPencil.weighted P c (fun _ => 1) =
    BoundedProjectionBasisGram.gram P c := by
  apply Matrix.ext
  intro i j
  simp only [BoundedProjectionBasisPencil.weighted, BoundedProjectionBasisGram.gram,
    BoundedProjectionBasisGram.matrix, mul_one]
  change _ = ∑ x, _
  rfl

theorem linear_packet (P : Readers) (unit : Bool) (c : List Bool) (h : ℤ)
    (d : BoundedProjectionMoments.Feature P c) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionProbeEntries.linear P unit (row P c h d.val i j) : ℚ) =
      BoundedProjectionBasisPencil.weighted P c (featureFunction P c unit d) i j := by
  cases unit with
  | true =>
    unfold BoundedProjectionProbeEntries.linear featureFunction
    change (BoundedProjectionProbeEntries.gram P (row P c h d.val i j) : ℚ) =
      BoundedProjectionBasisPencil.weighted P c (fun _ => 1) i j
    rw [gram_packet, unit_weighted]
  | false =>
    have hq : BoundedProjectionProbeEntries.featureQuery (row P c h d.val i j) =
        pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val))) := by
      simp only [BoundedProjectionProbeEntries.featureQuery, row, context, BoundedProjectionProbeEntries.context,
        BoundedProjectionProbeEntries.hashContext, BoundedProjectionProbeEntries.featureCode, pairFst_pair, pairSnd_pair, hash_original]
    unfold BoundedProjectionProbeEntries.linear featureFunction
    change (BoundedProjectionFeatureMoments.moment P (BoundedProjectionProbeEntries.featureQuery (row P c h d.val i j)) : ℚ) = _
    rw [hq, BoundedProjectionFeatureMoments.moment_packet]
    unfold BoundedProjectionBasisPencil.weighted
    apply Finset.sum_congr rfl
    intro x _
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring

theorem matrix_packet (P : Readers) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedProjectionMoments.Feature P c) :
    ((BoundedProjectionProbeEntries.matrix P unit (context P c h d.val)).submatrix
      (indexEquiv P c h d.val) (indexEquiv P c h d.val)).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
        BoundedProjectionSignatureProbe.matrix P c (featureFunction P c unit d) h := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, BoundedProjectionProbeEntries.matrix, indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (BoundedProjectionProbeEntries.constant P (row P c h d.val i j) : ℚ) +
    C (BoundedProjectionProbeEntries.linear P unit (row P c h d.val i j) : ℚ) * X = _
  rw [constant_packet, linear_packet]
  rfl

theorem determinant_packet (P : Readers) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedProjectionMoments.Feature P c) :
    (BoundedProjectionProbeEntries.matrix P unit (context P c h d.val)).det.map (Int.castRingHom ℚ) =
      (BoundedProjectionSignatureProbe.matrix P c (featureFunction P c unit d) h).det := by
  let A := BoundedProjectionProbeEntries.matrix P unit (context P c h d.val)
  let e := indexEquiv P c h d.val
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) := ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P unit c h d)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem coefficient_packet (P : Readers) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedProjectionMoments.Feature P c) :
    (BoundedProjectionProbeCoefficient.firstCoefficient P unit (context P c h d.val) : ℚ) =
      (BoundedProjectionSignatureProbe.matrix P c (featureFunction P c unit d) h).det.coeff 1 := by
  have H := congrArg (fun p : ℚ[X] => p.coeff 1) (determinant_packet P unit c h d)
  unfold BoundedProjectionProbeCoefficient.firstCoefficient
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using H

theorem sign_packet (P : Readers) (unit : Bool) (c : List Bool) (h : ℤ) (d : BoundedProjectionMoments.Feature P c) :
    SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P unit (context P c h d.val)) =
      SignType.sign ((BoundedProjectionSignatureProbe.matrix P c (featureFunction P c unit d) h).det.coeff 1) := by
  rw [← coefficient_packet]
  exact (sign_intCast _).symm

end LeanCanny.Encoding.BoundedProjectionProbeSource
