/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
public import LeanCanny.Encoding.IntegralFramedPhysicalIntegerLeaves
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Algebra.DiagonalUnivariateSystem
/-! # Literal integer leaf readers use the exact physical clearing recipe -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafRecipe
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def arguments (B : IntegralFramedBankQuery.Bank) (c : List Bool) :=
  CoefficientBankTermQuery.ofSnapshot B.parameters B.plan B.data (B.key c)
    (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c))
    (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data (B.key c)).scalar

noncomputable def reader (B : IntegralFramedBankQuery.Bank) (Q : IntegerPolynomialRootQueriesBits.Source)
    (c w : List Bool) (i : ℕ) :=
  IntegralFramedPhysicalIntegerLeaves.value B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    B.key B.positive Q (pair (pair c w) (BinaryNatCode.encode i))

private theorem scalar_recipe (B : IntegralFramedBankQuery.Bank)
    (Q : IntegerPolynomialRootQueriesBits.Source) (c : List Bool) (i : ℕ)
    (hi : i < (family B.parameters B.plan B.data).birth (B.key c)) :
    CoefficientBankLeafQuery.polynomial (arguments B c) (Q.polynomial (pair c (BinaryNatCode.encode i)))
      (2*Q.degree (pair c (BinaryNatCode.encode i))) i =
    ((IntegralFramedPhysicalUnivariateTest.source B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      B.key (IntegralFramedPhysicalIntegerLeaves.coordinate B.parameters B.plan B.data B.key B.positive) Q).polynomial
      (pair c (BinaryNatCode.encode i))).toMvPolynomial
        (IntegralFramedPhysicalUnivariateTest.column B.parameters B.plan B.data B.key
          (IntegralFramedPhysicalIntegerLeaves.coordinate B.parameters B.plan B.data B.key B.positive) c
          (BinaryNatCode.encode i)) := by
  rw [CoefficientBankLeafQuery.polynomial_native (arguments B c) Q _ i hi]
  have hp : (family B.parameters B.plan B.data).birth (B.key c)-1-
      ((family B.parameters B.plan B.data).birth (B.key c)-1-i) = i := by omega
  unfold IntegralFramedPhysicalUnivariateTest.source IntegralMixedFramedBankUnivariateSource.source
  unfold IntegerPolynomialRationalPointSource.source
  dsimp only [IntegerPolynomialExpandSource.source, IntegerPolynomialRationalPointSource.clearedSource,
    IntegerPolynomialRationalPointSource.linear, IntegerPolynomialRationalPointSource.constant]
  simp only [CoefficientBankLeafQuery.scalars, arguments, CoefficientBankTermQuery.ofSnapshot,
    IntegralMixedFramedBankScalars.scalars, IntegralMixedFramedBankUnivariateSource.power,
    IntegralFramedPhysicalUnivariateTest.saved, IntegralFramedPhysicalUnivariateTest.selected,
    IntegralFramedPhysicalIntegerLeaves.coordinate_packet, pairFst_pair, pairSnd_pair]
  have hp' : (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count-1-
      ((family B.parameters B.plan B.data).birth (B.key c)-1-i) = i := hp
  rw [hp']
  simp only [IntegralFramedPhysicalUnivariateTest.column, IntegralFramedPhysicalIntegerLeaves.coordinate,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

/-- The actual native untruncated leaf reader, evaluated at its OWN complete
physical word. No generator homomorphism or sign model is supplied. -/
theorem value (B : IntegralFramedBankQuery.Bank) (Q : IntegerPolynomialRootQueriesBits.Source)
    (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (i : ℕ) (hi : i < (family B.parameters B.plan B.data).birth (B.key c)) :
    IntegralFramedPhysicalIntegerLeaves.value B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      B.key B.positive Q (pair (pair c w) (BinaryNatCode.encode i)) =
    InfinitesimalSign.encode (SignType.sign
      ((CoefficientBankLeafQuery.polynomial (arguments B c) (Q.polynomial (pair c (BinaryNatCode.encode i)))
        (2*Q.degree (pair c (BinaryNatCode.encode i))) i).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val)) := by
  unfold IntegralFramedPhysicalIntegerLeaves.value IntegralFramedPhysicalUnivariateTest.value
  rw [SquareSampleCompleteUnivariateTest.packet _ _ _ c w (BinaryNatCode.encode i) hw]
  rw [scalar_recipe B Q c i hi]
  apply congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v))
  exact (DiagonalUnivariateSystem.eval _ _ (Int.castRingHom ℝ)
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val).symm

end LeanCanny.Encoding.CoefficientMarkedRecordLeafRecipe
