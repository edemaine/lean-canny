/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSignSpace
public import LeanCanny.ETR.TubeCoefficientBounds

/-! # Derived degree and coefficient-mass budgets for the tube sign queries

The stored margin's raw integer numerator and positive denominator avoid
rational normalization. Fixed clearing allowances give uniform output budgets
from coordinate degree and mass bounds. No bound on suitably chosen coordinate
representations in the original ETR input size is asserted.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding MvPolynomial
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

theorem zeroMarginConstraint_mass (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    MvMass.mass (zeroMarginConstraint c i) ≤ MvMass.mass (CompactSource.polynomial (pairFst c)) + 3 := by
  have hp : MvMass.mass (samplePolynomial c) ≤ MvMass.mass (CompactSource.polynomial (pairFst c)) :=
    MvMass.rename_le _ _
  rcases i with b | ⟨j, b⟩ <;> cases b
  · exact (MvMass.add_le _ _).trans (by simp only [MvMass.X]; omega)
  · exact (MvMass.add_le _ _).trans (by simp only [MvMass.neg, MvMass.X]; omega)
  · have h1 := MvMass.add_le (X (sampleIndex c (.inl j)) : MvPolynomial _ ℤ) 1
    have h2 := MvMass.add_le (X (sampleIndex c (.inl j)) + 1 : MvPolynomial _ ℤ)
      (X (sampleIndex c (.inr (.inr (j, false)))))
    simp only [MvMass.X, MvMass.one] at h1 h2
    exact h2.trans (by omega)
  · have h1 := MvMass.sub_le (1 : MvPolynomial (Fin (TubeParameter.spatialCount (pairFst c))) ℤ)
      (X (sampleIndex c (.inl j)))
    have h2 := MvMass.add_le (1 - X (sampleIndex c (.inl j)) : MvPolynomial _ ℤ)
      (X (sampleIndex c (.inr (.inr (j, true)))))
    simp only [MvMass.X, MvMass.one] at h1 h2
    exact h2.trans (by omega)

theorem integerConstraint_mass (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    MvMass.mass (integerConstraint c i) ≤ marginDenominator c *
      (MvMass.mass (CompactSource.polynomial (pairFst c)) + 3) + (marginNumerator c).natAbs := by
  unfold integerConstraint
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add
  · apply (MvMass.mul_le _ _).trans
    rw [MvMass.C, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (zeroMarginConstraint_mass c i)
  · cases i with
    | inl _ => exact (MvMass.zero.le).trans (Nat.zero_le _)
    | inr _ => exact (MvMass.C _).le

noncomputable def constraintMassBits (c : List Bool) : ℕ :=
  width c + 1 + (CompactSource.size (pairFst c) + 2 * CompactSource.size (pairFst c) ^ 2) + 3

theorem constraintMassBits_unary : UnaryFn constraintMassBits :=
  ((width_unary.add (UnaryFn.const 1)).add
    ((CompactSource.size_unary.comp pairFst_mem_FP).add
      ((UnaryFn.const 2).mul ((CompactSource.size_unary.comp pairFst_mem_FP).pow_const 2)))).add (UnaryFn.const 3)

theorem integerConstraint_mass_pow (c : List Bool) (i : PerturbedSource.Index (pairFst c)) :
    RationalSubstitution.sourceMass (integerConstraint c i) ≤ 2 ^ constraintMassBits c := by
  have hd := denominatorNat_bound c (alphaIndex c + 1)
  have hn := integer_bound c (alphaIndex c + 1)
  have hp := CompactSource.polynomial_mass (pairFst c)
  have hden : marginDenominator c ≤ 2 ^ (width c + 1) := hd
  have hnum : (marginNumerator c).natAbs ≤ 2 ^ (width c + 1) := hn
  let e := CompactSource.size (pairFst c) + 2 * CompactSource.size (pairFst c) ^ 2
  change MvMass.mass (integerConstraint c i) ≤ _
  apply (integerConstraint_mass c i).trans
  calc
    _ ≤ 2 ^ (width c + 1) * (MvMass.mass (CompactSource.polynomial (pairFst c)) + 3) +
        2 ^ (width c + 1) := Nat.add_le_add (Nat.mul_le_mul_right _ hden) hnum
    _ = 2 ^ (width c + 1) * (MvMass.mass (CompactSource.polynomial (pairFst c)) + 4) := by ring
    _ ≤ 2 ^ (width c + 1) * (2 ^ e + 4) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hp 4)
    _ ≤ 2 ^ (width c + 1) * 2 ^ (e + 3) := by
      apply Nat.mul_le_mul_left
      rw [pow_add 2 e 3]
      have h := Nat.one_le_two_pow (n := e)
      norm_num
      omega
    _ = 2 ^ constraintMassBits c := by rw [← pow_add]; rfl

noncomputable def queryWeight (c : List Bool) : ℕ :=
  TubeParameter.spatialCount (pairFst c) * (2 * TubeIndexed.degreeBound (pairFst c))

theorem queryWeight_unary : UnaryFn queryWeight :=
  (TubeParameter.spatialCount_unary.comp pairFst_mem_FP).mul
    ((UnaryFn.const 2).mul (TubeIndexed.degreeBound_unary.comp pairFst_mem_FP))

theorem clearing_sum (c : List Bool) :
    (∑ _j : Fin (TubeParameter.spatialCount (pairFst c)), 2 * TubeIndexed.degreeBound (pairFst c)) = queryWeight c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, queryWeight]

theorem signQuery_degree (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (E : ℕ)
    (hn : ∀ j, (d.numerator j).natDegree ≤ E) (hd : ∀ j, (d.denominator j).natDegree ≤ E)
    (i : PerturbedSource.Index (pairFst c)) :
    (signQuery c mask ell alpha d i).natDegree ≤ queryWeight c * E := by
  unfold signQuery
  split_ifs
  · simp
  · exact (RationalSubstitution.natDegree_clearedWith_le _ _ _ _ (integerConstraint_degreeOf c i) E hn hd).trans_eq
      (by rw [clearing_sum])

theorem signQuery_mass (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) (b : ℕ)
    (hn : ∀ j, coefficientMass (d.numerator j) ≤ 2 ^ b)
    (hd : ∀ j, coefficientMass (d.denominator j) ≤ 2 ^ b)
    (i : PerturbedSource.Index (pairFst c)) :
    coefficientMass (signQuery c mask ell alpha d i) ≤ 2 ^ (constraintMassBits c + queryWeight c * b) := by
  unfold signQuery
  split_ifs
  · rw [← Polynomial.C_1, coefficientMass_C]
    exact Nat.one_le_two_pow
  · exact (RationalSubstitution.coefficientMass_clearedWith_le_pow _ _ _ _ (integerConstraint_degreeOf c i)
      (constraintMassBits c) b (integerConstraint_mass_pow c i) hn hd).trans_eq (by rw [clearing_sum])

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelSign
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

/-- Bounds on the coordinate data suffice; bounds on the expanded queries are derived. -/
structure CoordinateBudget (S : Source) where
  rootDegree : List Bool → List Bool
  rootMass : List Bool → List Bool
  degree : List Bool → List Bool
  mass : List Bool → List Bool
  rootDegreeFP : rootDegree ∈ FP
  rootMassFP : rootMass ∈ FP
  degreeFP : degree ∈ FP
  massFP : mass ∈ FP
  rootDegree_pos : ∀ c, 0 < Nat.fromBitsLE (rootDegree c)
  root_degree : ∀ c, (S.coordinates c).polynomial.natDegree ≤ Nat.fromBitsLE (rootDegree c)
  root_mass : ∀ c, coefficientMass (S.coordinates c).polynomial ≤ 2 ^ Nat.fromBitsLE (rootMass c)
  numerator_degree : ∀ c j, ((S.coordinates c).numerator j).natDegree ≤ Nat.fromBitsLE (degree c)
  denominator_degree : ∀ c j, ((S.coordinates c).denominator j).natDegree ≤ Nat.fromBitsLE (degree c)
  numerator_mass : ∀ c j, coefficientMass ((S.coordinates c).numerator j) ≤ 2 ^ Nat.fromBitsLE (mass c)
  denominator_mass : ∀ c j, coefficientMass ((S.coordinates c).denominator j) ≤ 2 ^ Nat.fromBitsLE (mass c)

namespace CoordinateBudget
variable {S : Source}

noncomputable def degreeCode (B : CoordinateBudget S) (c : List Bool) : List Bool :=
  BinaryNat.mul (pair (BinaryNatCode.encode (queryWeight (S.packet c))) (B.degree c))

noncomputable def massCode (B : CoordinateBudget S) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNatCode.encode (constraintMassBits (S.packet c)))
    (BinaryNat.mul (pair (BinaryNatCode.encode (queryWeight (S.packet c))) (B.mass c))))

theorem degreeCode_eq (B : CoordinateBudget S) (c : List Bool) :
    degreeCode B c = BinaryNatCode.encode (queryWeight (S.packet c) * Nat.fromBitsLE (B.degree c)) := by
  simp only [degreeCode, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem massCode_eq (B : CoordinateBudget S) (c : List Bool) :
    massCode B c = BinaryNatCode.encode
      (constraintMassBits (S.packet c) + queryWeight (S.packet c) * Nat.fromBitsLE (B.mass c)) := by
  simp only [massCode, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem degreeCode_FP (B : CoordinateBudget S) (hp : S.packet ∈ FP) : degreeCode B ∈ FP := by
  have hw := bits_mem_FP (queryWeight_unary.comp hp)
  exact mem_FP_comp (mem_FP_pair hw B.degreeFP) BinaryNat.mul_mem_FP

theorem massCode_FP (B : CoordinateBudget S) (hp : S.packet ∈ FP) : massCode B ∈ FP := by
  have hw := bits_mem_FP (queryWeight_unary.comp hp)
  have hs := bits_mem_FP (constraintMassBits_unary.comp hp)
  have hm := mem_FP_comp (mem_FP_pair hw B.massFP) BinaryNat.mul_mem_FP
  exact mem_FP_comp (mem_FP_pair hs hm) BinaryNat.add_mem_FP

noncomputable def budget (B : CoordinateBudget S) : Budget S where
  rootDegree := B.rootDegree
  rootMass := B.rootMass
  degree := B.degreeCode
  mass := B.massCode
  rootDegree_pos := B.rootDegree_pos
  root_degree := B.root_degree
  root_mass := B.root_mass
  query_degree := by
    intro c i hi
    rw [B.degreeCode_eq]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold indexedSignQuery
    rw [dite_eq_left hi]
    exact signQuery_degree _ _ _ _ _ _ (B.numerator_degree c) (B.denominator_degree c) _
  query_mass := by
    intro c i hi
    rw [B.massCode_eq]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold indexedSignQuery
    rw [dite_eq_left hi]
    exact signQuery_mass _ _ _ _ _ _ (B.numerator_mass c) (B.denominator_mass c) _

theorem controls (B : CoordinateBudget S) (hp : S.packet ∈ FP) :
    SignPatternBits.ControlsPolyTime (family S B.budget) :=
  TubeLevelSign.controls S B.budget hp B.rootDegreeFP (B.degreeCode_FP hp) B.rootMassFP (B.massCode_FP hp)

theorem countEvaluator (B : CoordinateBudget S) (hp : S.packet ∈ FP)
    (a : SignPatternBits.Access (family S B.budget))
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (sampleCount S c)) :=
  TubeLevelSign.countEvaluator a (B.controls hp) H P

theorem sampleLanguage_mem_PSPACE (B : CoordinateBudget S) (hp : S.packet ∈ FP)
    (a : SignPatternBits.Access (family S B.budget))
    (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    sampleLanguage S ∈ PSPACE :=
  TubeLevelSign.sampleLanguage_mem_PSPACE a (B.controls hp) H P

end CoordinateBudget
end LeanCanny.ETR.TubeLevelSign
