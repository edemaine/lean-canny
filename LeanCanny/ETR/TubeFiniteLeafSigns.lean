/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignResidue
public import LeanCanny.ETR.TubeFiniteLeafSubstitution
public import LeanCanny.ETR.TubeLevelSignBounds

/-! # Streamed tube constraints on a finite product of algebraic roots

The complete integer constraints instantiate the finite-leaf sign source.
Their monomial counts remain binary; neither expanded constraints nor
intermediate rational-coordinate coefficient readers are supplied.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeFiniteLeafSigns
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
set_option backward.isDefEq.respectTransparency false

variable (packet : List Bool → List Bool) (pattern : List Bool → ℕ → SignType)

noncomputable def row (c : List Bool) (j : ℕ) : PerturbedSource.Index (pairFst (packet c)) :=
  TubeConstraintCoefficient.decodedRow id (fun _ => BinaryNatCode.encode j) (packet c)

noncomputable def source : FiniteLeafSignBits.Source (TubeSampleCoefficient.A packet) where
  count c := constraintCount (TubeIndexed.arity (pairFst (packet c)))
  terms c := FixedWidthPolynomial.count (TubeSampleCoefficient.A packet c) (TubeConstraintIndexed.blockWidth packet c)
  degree c := TubeIndexed.degreeBound (pairFst (packet c))
  height c := constraintMassBits (packet c)
  coefficient c j r := TubeConstraintIndexed.coefficientAt (packet c) (BinaryNatCode.encode j) r
  exponent c _ r i := FixedWidthPolynomial.entry (TubeConstraintIndexed.blockWidth packet c) r i
  pattern := pattern
  exponent_le c _ r _ i _ := (FixedWidthPolynomial.entry_lt _ _ _).le.trans (TubeIndexed.clearingWidth_le _)
  coefficient_le c j r _ := by
    change ((integerConstraint (packet c) (row packet c j)).coeff _).natAbs ≤ _
    exact (MvMass.coeff_le _ _).trans (integerConstraint_mass_pow (packet c) _)

theorem polynomial_eq (c : List Bool) (j : ℕ) :
    (source packet pattern).polynomial c j = integerConstraint (packet c) (row packet c j) := by
  unfold FiniteLeafSignBits.Source.polynomial source TubeConstraintIndexed.coefficientAt row
  apply FixedWidthPolynomial.indexed_source_eq
  intro e he i
  exact ((MvPolynomial.monomial_le_degreeOf i he).trans
    (integerConstraint_degreeOf _ _ i)).trans_lt (TubeIndexed.degreeBound_lt _)

theorem sign_eq (c : List Bool) (j : ℕ) (z : Fin (TubeSampleCoefficient.A packet c) → ℝ) :
    SignType.sign (((source packet pattern).polynomial c j).eval₂ (Int.castRingHom ℝ) z) =
      SignType.sign (Geometry.PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst (packet c)))
        (epsilon (packet c) : ℝ) (Geometry.TubePolynomial.splitPoint (samplePoint (packet c) z))
        (row packet c j)) := by
  rw [polynomial_eq, eval_integerConstraint, sign_mul,
    sign_pos (by exact_mod_cast marginDenominator_pos (packet c)), one_mul]

theorem row_of_constraint (c : List Bool) (i : PerturbedSource.Index (pairFst (packet c))) :
    row packet c (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val = i := by
  unfold row
  apply TubeConstraintCoefficient.decodedRow_of_code
  exact Nat.fromBitsLE_bits _

noncomputable def access (hp : packet ∈ FP)
    (readPattern : List Bool → List Bool) (hs : readPattern ∈ FP)
    (hpattern : ∀ c j, readPattern (pair c (BinaryNatCode.encode j)) = InfinitesimalSign.encode (pattern c j)) :
    (source packet pattern).Access where
  coefficient := TubeConstraintIndexed.value (packet ∘ pairFst) pairSnd
  exponent := FixedWidthPolynomial.exponentRead ((TubeSampleCoefficient.A packet) ∘ pairFst)
    ((TubeConstraintIndexed.blockWidth packet) ∘ pairFst)
  pattern := readPattern
  count_unary := TubeZero.constraintCount_unary (TubeSampleCoefficient.n_unary packet hp)
  terms_binary := BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP
    (TubeSampleCoefficient.A_unary packet hp) (TubeConstraintIndexed.blockWidth_unary packet hp))
      (FixedWidthPolynomial.countCode_code _ _))
  degree_binary := BinaryFn.of_bits (bits_mem_FP
    (TubeIndexed.degreeBound_unary.comp (mem_FP_comp hp pairFst_mem_FP)))
  height_binary := BinaryFn.of_bits (bits_mem_FP (constraintMassBits_unary.comp hp))
  coefficientEvaluator := TubeConstraintIndexed.evaluator _ _ (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP
  exponent_FP := FixedWidthPolynomial.exponentRead_mem_FP
    ((TubeSampleCoefficient.A_unary packet hp).comp pairFst_mem_FP)
    ((TubeConstraintIndexed.blockWidth_unary packet hp).comp pairFst_mem_FP)
  pattern_FP := hs
  coefficient_eq q r _ m hm := by
    rw [TubeConstraintIndexed.value_packet _ _ q r m hm]
    unfold source
    simp only [TubeConstraintIndexed.coefficient, TubeConstraintIndexed.coefficientAt,
      TubeConstraintCoefficient.decodedRow, TubeConstraintCoefficient.cappedRow,
      Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  exponent_eq q r _ i hi := by
    rw [FixedWidthPolynomial.exponentRead_packet _ _ q r i hi]
    exact Nat.fromBitsLE_bits _
  pattern_eq := hpattern

/-- Original algebraic coordinates realizing the requested tube signs. -/
def language (B : SeparableBits.Family) : Language := {c |
  ∃ z : Fin (TubeSampleCoefficient.A packet c) → ℝ,
    (∀ i, (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (z i) = 0) ∧
    ∀ j : Fin (constraintCount (TubeIndexed.arity (pairFst (packet c)))),
      SignType.sign (Geometry.PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst (packet c)))
        (epsilon (packet c) : ℝ) (Geometry.TubePolynomial.splitPoint (samplePoint (packet c) z))
        (row packet c j.val)) = pattern c j.val}

theorem language_eq (B : SeparableBits.Family) :
    language packet pattern B = FiniteLeafSignBits.finiteSignLanguage B (TubeSampleCoefficient.A packet)
      (source packet pattern) := by
  ext c
  change (∃ z, _ ∧ _) ↔ (∃ z, _ ∧ _)
  apply exists_congr
  intro z
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  change _ ↔ _ = pattern c j.val
  rw [sign_eq]

theorem language_mem_PSPACE (B : SeparableBits.Family) (R : SeparableBits.Readers B)
    (D b : List Bool → ℕ)
    (hne : ∀ c i, i < TubeSampleCoefficient.A packet c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < TubeSampleCoefficient.A packet c →
      (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hheight : ∀ c i, i < TubeSampleCoefficient.A packet c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)
    (hp : packet ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b)
    (readPattern : List Bool → List Bool) (hs : readPattern ∈ FP)
    (hpattern : ∀ c j, readPattern (pair c (BinaryNatCode.encode j)) = InfinitesimalSign.encode (pattern c j)) :
    language packet pattern B ∈ PSPACE := by
  rw [language_eq]
  exact FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE B (TubeSampleCoefficient.A packet) D b
    hne hdegree hheight (source packet pattern) (access packet pattern hp readPattern hs hpattern)
    R (TubeSampleCoefficient.A_unary packet hp) hD hb

/-- No exact original degree or rational-coordinate computation is supplied. -/
theorem language_mem_PSPACE_from_residues (B : SeparableBits.Family) (D b : List Bool → ℕ)
    (hne : ∀ c i, i < TubeSampleCoefficient.A packet c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < TubeSampleCoefficient.A packet c →
      (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hmass : ∀ c i, i < TubeSampleCoefficient.A packet c →
      coefficientMass (B.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c)
    (hp : packet ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient B.polynomial))
    (readPattern : List Bool → List Bool) (hs : readPattern ∈ FP)
    (hpattern : ∀ c j, readPattern (pair c (BinaryNatCode.encode j)) = InfinitesimalSign.encode (pattern c j)) :
    language packet pattern B ∈ PSPACE := by
  rw [language_eq]
  exact FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE_from_residues B (TubeSampleCoefficient.A packet) D b
    hne hdegree hmass (source packet pattern) (access packet pattern hp readPattern hs hpattern)
    (TubeSampleCoefficient.A_unary packet hp) hD hb E

end LeanCanny.ETR.TubeFiniteLeafSigns
