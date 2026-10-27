/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockReaders

/-! # Native multivariate term families in sample coordinate blocks

Variable zero retains the actual sample parameter. Remaining variables are
the free coordinate block. Native readers stream the exact collected integer
coefficients by binary monomial rank; no expanded polynomial is serialized.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockTerm
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Brackets
open BoundedCriticalSampleBlockSource BoundedCriticalSampleBlockEncoding
open scoped Classical BigOperators
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass

noncomputable def polynomial (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    MvPolynomial (Fin (k u + 1)) ℤ :=
  IndexedMultivariateRational.cleared (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount
    (2 * ((source read).syntax u).toData.size) ((source read).syntax u).monomialCoefficient
    ((source read).syntax u).monomialExponent (coordinate P o k true u) (coordinate P o k false u)

theorem polynomial_degree (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    (polynomial P read o k u).totalDegree ≤ BivariateRationalTermReader.weight (source read) u * extent P u := by
  have H := IndexedMultivariateRational.totalDegree_cleared_le
    (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount
    (2 * ((source read).syntax u).toData.size) (extent P u)
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (coordinate P o k true u) (coordinate P o k false u)
    (fun r _ i _ => BivariateRationalTermReader.exponent_bound (source read) u r i)
    (fun i _ => coordinate_degree P o k true u i) (fun i _ => coordinate_degree P o k false u i)
  simpa only [polynomial, BivariateRationalTermReader.weight, BivariateTermReader.size_eq] using H

theorem support_fits (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool)
    (m : Fin (k u + 1) →₀ ℕ) (hm : m ∈ (polynomial P read o k u).support) (i : Fin (k u + 1)) :
    m i < 2 ^ width P read u :=
  ((MvPolynomial.monomial_le_degreeOf i hm).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
    ((polynomial_degree P read o k u).trans_lt (clearing_lt P read u))

noncomputable def compiled (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) :=
  (BoundedCriticalSampleBlockReaders.coordinates P read o k (source read)).family

theorem encode_polynomial (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    FixedWidthKronecker.encode (k u + 1) (width P read u) (polynomial P read o k u) = (compiled P read o k).polynomial u := by
  simp only [polynomial, IndexedMultivariateRational.encode_cleared, encode_coordinate, compiled,
    RationalSubstitutionBits.Coordinates.family, RationalSubstitutionBits.Source.family,
    BoundedCriticalSampleBlockReaders.coordinates, RationalSubstitution.IntegerBits.Family.polynomial]

noncomputable def coefficient (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) : List Bool → List Bool :=
  (compiled P read o k).value
theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P read o k) :=
  (BoundedCriticalSampleBlockReaders.coordinates P read o k (source read)).evaluator
    (RationalSubstitutionBits.Source.ofTerm_polyTime hr)
    (BoundedCriticalSampleBlockReaders.evaluator h read hr ho hk true ha)
    (BoundedCriticalSampleBlockReaders.evaluator h read hr ho hk false ha)

theorem coefficient_packet (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool)
    (r : Fin (FixedWidthPolynomial.count (k u + 1) (width P read u))) (m : ℕ) (hm : 0 < m) :
    coefficient P read o k (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((polynomial P read o k u).coeff (FixedWidthPolynomial.vector _ _ r) : ℤ) : ZMod m) := by
  rw [coefficient, RationalSubstitution.IntegerBits.Family.value_packet _ _ m hm]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [← encode_polynomial, FixedWidthKronecker.coefficient _ _ _ (support_fits P read o k u) r]
  rfl

noncomputable def mass (P : Readers) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  2 * ((source read).normalized u).length + 1 + BivariateRationalTermReader.weight (source read) u *
    BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)

theorem encoded_mass (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    coefficientMass ((compiled P read o k).polynomial u) ≤ 2 ^ mass P read u := by
  have H := RationalSubstitution.Indexed.coefficientMass_cleared_le_pow
    (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount
    (2 * ((source read).syntax u).toData.size) ((source read).syntax u).toData.size
    (BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u))
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (encoded P read o k true u) (encoded P read o k false u)
    (fun r _ i _ => BivariateRationalTermReader.exponent_bound (source read) u r i)
    (fun r _ => ((source read).syntax u).monomialCoefficient_natAbs_le_pow_dataSize r)
    (fun i _ => BoundedCriticalSampleBlockEncoding.encoded_mass P read o k true u i)
    (fun i _ => BoundedCriticalSampleBlockEncoding.encoded_mass P read o k false u i)
  apply H.trans (Nat.pow_le_pow_right (by decide) ?_)
  have hc := ((source read).syntax u).monomialCount_size_le
  unfold mass BivariateRationalTermReader.weight
  rw [BivariateTermReader.size_eq]
  omega

theorem coefficient_bound (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool)
    (r : Fin (FixedWidthPolynomial.count (k u + 1) (width P read u))) :
    ((polynomial P read o k u).coeff (FixedWidthPolynomial.vector _ _ r)).natAbs ≤ 2 ^ mass P read u := by
  rw [← FixedWidthKronecker.coefficient _ _ _ (support_fits P read o k u) r, encode_polynomial]
  exact (coeff_natAbs_le_coefficientMass _ _).trans (encoded_mass P read o k u)

theorem polynomial_mass (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool) :
    MvMass.mass (polynomial P read o k u) ≤ 2 ^ (span P read k u + mass P read u) := by
  rw [← FixedWidthPolynomial.sum_monomials_eq (k u + 1) (width P read u) _ (support_fits P read o k u)]
  calc
    _ ≤ ∑ r : Fin (FixedWidthPolynomial.count (k u + 1) (width P read u)),
        MvMass.mass (MvPolynomial.monomial (FixedWidthPolynomial.vector _ _ r)
          ((polynomial P read o k u).coeff (FixedWidthPolynomial.vector _ _ r))) := MvMass.sum_le _ _
    _ ≤ ∑ _r : Fin (FixedWidthPolynomial.count (k u + 1) (width P read u)), 2 ^ mass P read u := by
      apply Finset.sum_le_sum
      intro r _
      rw [MvMass.monomial]
      exact coefficient_bound P read o k u r
    _ = FixedWidthPolynomial.count (k u + 1) (width P read u) * 2 ^ mass P read u := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = _ := by rw [FixedWidthPolynomial.count, ← pow_mul, ← pow_add]; rfl

theorem sign_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) :
    SignType.sign ((polynomial P read o k (pair c r)).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y)) =
        SignType.sign ((TermView.term (read (pair c r))).eval (assignment x.val (o (pair c r)) (k (pair c r)) y)) := by
  let u := pair c r
  let v := environment _ (BoundedCriticalSampleLabels.parameter P c x).val y
  let env := fun i => (coordinate P o k true u i).eval₂ (Int.castRingHom ℝ) v /
    (coordinate P o k false u i).eval₂ (Int.castRingHom ℝ) v
  have H := IndexedMultivariateRational.sign_eval₂_cleared (Int.castRingHom ℝ) v
    (Nat.fromBitsLE ((source read).arity u)) ((source read).syntax u).monomialCount ((source read).syntax u).toData.size
    ((source read).syntax u).monomialCoefficient ((source read).syntax u).monomialExponent
    (coordinate P o k true u) (coordinate P o k false u)
    (fun r _ i _ => BivariateRationalTermReader.exponent_bound (source read) u r i)
    (fun i _ => denominator_nonzero P o k c r x y i)
  have HS := ((source read).syntax u).eval₂_indexed_source env _ ((source read).scope u)
  have HE : env = assignment x.val (o u) (k u) y := funext (fun i => coordinate_eval P o k c r x y i)
  refine H.trans ((congrArg SignType.sign HS).trans ?_)
  rw [HE]
  rfl

theorem sign_finite_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) (hk : o (pair c r) + k (pair c r) ≤ P.dim c + 4) :
    SignType.sign ((polynomial P read o k (pair c r)).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y)) =
        SignType.sign ((TermView.term (read (pair c r))).eval
          (Formula.extend (finiteAssignment x.val (o (pair c r)) (k (pair c r)) y))) := by
  rw [sign_sample, assignment_finite x.val _ _ y hk]

theorem zero_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) :
    (polynomial P read o k (pair c r)).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y) = 0 ↔
        (TermView.term (read (pair c r))).eval (assignment x.val (o (pair c r)) (k (pair c r)) y) = 0 := by
  rw [← sign_eq_zero_iff, sign_sample P read o k c r x y, sign_eq_zero_iff]

theorem sign_empty_sample (P : Readers) (read : List Bool → List Bool) (o : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin 0 → ℝ) :
    SignType.sign ((polynomial P read o (fun _ => 0) (pair c r)).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y)) =
        SignType.sign ((TermView.term (read (pair c r))).eval (Formula.extend x.val)) := by
  rw [sign_sample P read o (fun _ => 0) c r x y, assignment_empty]

/-- Freezing the first coordinate at its original value agrees in sign with
the smaller block. The sample parameter stays fixed in both families. -/
theorem sign_drop_first_sample (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (y : Fin (k (pair c r)) → ℝ) :
    SignType.sign ((polynomial P read o (fun u => k u + 1) (pair c r)).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter P c x).val
        (environment _ (Formula.extend x.val (o (pair c r))) y))) =
      SignType.sign ((polynomial P read (fun u => o u + 1) k (pair c r)).eval₂ (Int.castRingHom ℝ)
        (environment _ (BoundedCriticalSampleLabels.parameter P c x).val y)) := by
  rw [sign_sample P read o (fun u => k u + 1) c r x
    (environment _ (Formula.extend x.val (o (pair c r))) y),
    sign_sample P read (fun u => o u + 1) k c r x y, assignment_drop_first]

theorem degree_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (fun u => BivariateRationalTermReader.weight (source read) u * extent P u) :=
  (BivariateRationalTermReader.weight_binary (source read) (RationalSubstitutionBits.Source.ofTerm_polyTime hr)).mul (extent_binary h)

theorem mass_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) : BinaryFn (mass P read) := by
  have hs : (source read).PolyTime := RationalSubstitutionBits.Source.ofTerm_polyTime hr
  have hn := BinaryFn.ofUnary (UnaryFn.length ((source read).normalized_mem_FP hs))
  have hw := BivariateRationalTermReader.weight_binary (source read) hs
  exact (((BinaryFn.const 2).mul hn).add (BinaryFn.const 1)).add
    (hw.mul ((BoundedCriticalRationalCoordinates.coordinateMass_binary h).comp pairFst_mem_FP))

theorem polynomial_mass_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : BinaryFn (fun u => span P read k u + mass P read u) :=
  (BinaryFn.ofUnary (span_unary h read hr hk)).add (mass_binary h read hr)

theorem index_count_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) :
    BinaryFn (fun u => FixedWidthPolynomial.count (k u + 1) (width P read u)) :=
  ((BinaryFn.const 2).powUnary (span_unary h read hr hk)).of_eq (fun u => by
    simp only [FixedWidthPolynomial.count, ← pow_mul, span])

end LeanCanny.Encoding.BoundedCriticalSampleBlockTerm
