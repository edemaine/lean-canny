/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordLeafRecipe
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
/-! # Literal native bank terms at the same complete physical tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTermRecipe
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def reader (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c w : List Bool) :=
  IntegralFramedPhysicalBankTerm.value B T hr word (pair (pair c w) [])

noncomputable def polynomial (B : IntegralFramedBankQuery.Bank) (word : List Bool → List Bool) (c : List Bool) :=
  CoefficientBankTermQuery.polynomial (CoefficientMarkedRecordLeafRecipe.arguments B c)
    ((IntegralMixedFramedBankTermBits.source word).syntax (B.key c))

private theorem columns (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c : List Bool) :
    IntegralFramedPhysicalBankTerm.columns B T hr word c [] =
      (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data (B.key c)).scalar := by
  unfold IntegralFramedPhysicalBankTerm.columns
  rw [IntegralMixedFramedPhysicalIndex.nativeScalarColumn_eq]
  rfl

/-- This is equality with the actual common-cleared native reader, before
any sign interpretation at a different tuple or independently sampled word. -/
theorem value (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (word : List Bool → List Bool) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    reader B T hr word c w = InfinitesimalSign.encode (SignType.sign
      ((polynomial B word c).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val)) := by
  unfold reader IntegralFramedPhysicalBankTerm.value IntegralFramedPhysicalBankTerm.test
  rw [SquareSampleCompleteEmbeddedPolynomialTest.packet _ _ _ c w [] hw]
  simp only [IntegralFramedPhysicalBankTerm.source]
  rw [columns]
  unfold polynomial CoefficientMarkedRecordLeafRecipe.arguments
  rw [CoefficientBankTermQuery.polynomial_native]
  apply congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v))
  exact (MvPolynomial.eval₂_rename (Int.castRingHom ℝ)
    (IntegralFramedPhysicalSquare.sampler B.parameters B.plan B.data (B.key c)).scalar
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val
    (IntegralMixedFramedBankTermBits.polynomial B.parameters B.plan B.data word (B.key c))).symm

end LeanCanny.Encoding.CoefficientMarkedRecordTermRecipe
