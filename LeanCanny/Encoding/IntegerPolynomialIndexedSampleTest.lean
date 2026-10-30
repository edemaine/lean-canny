/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleInput
public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest

/-! # Indexed scalar tests at fixed complete integer-root labels

Extra query fields select a test polynomial while the original root source
and its complete label stay fixed. This supports streamed coefficient signs
over algebraic samples without regenerating the source or its labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialIndexedSampleTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegerPolynomialRootQueriesBits (Source)
open SquareSampleCompleteIndexedPolynomialTest (Test)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def normalize (z : List Bool) : List Bool := pair (pairFst z) (pairSnd z)
theorem normalize_FP : normalize ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def test (S Q : Source) : Test (IntegerPolynomialSampleInput.input S) where
  polynomial c d := (Q.polynomial (pair c d)).toMvPolynomial (0 : Fin 1)
  degree z := Q.degree (normalize z)
  mass z := Q.mass (normalize z)
  polynomial_degree z := (DiagonalUnivariateSystem.degree_le _ _).trans (Q.degree_bound (normalize z))
  polynomial_mass z := (DiagonalUnivariateSystem.mass_le _ _).trans (Q.mass_bound (normalize z))

theorem testAccess (S : Source) {Q : Source} (B : IntegerPolynomialRootQueriesBits.Access Q) : (test S Q).Access := by
  have hctx : (normalize ∘ RationalSubstitution.IntegerBits.context) ∈ FP :=
    mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP normalize_FP
  have hD : BinaryFn (Q.degree ∘ normalize) := B.degree.comp normalize_FP
  have hW : UnaryFn (fun z => (Q.degree (normalize z)).size) :=
    (UnaryFn.length hD.bits_mem_FP).of_eq (fun z => BinaryNatCode.length_encode (Q.degree (normalize z)))
  have P := PolynomialFamilyProductBits.reindexEvaluator B.coefficient (normalize ∘ RationalSubstitution.IntegerBits.context) hctx
  have E := UnivariateRowBits.evaluator (UnaryFn.const 1) (hW.comp RationalSubstitution.IntegerBits.context_mem_FP)
    (fun _ => (0 : Fin 1)) (UnaryFn.const 0) (Q.polynomial ∘ normalize ∘ RationalSubstitution.IntegerBits.context) P
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨hD, B.mass.comp normalize_FP, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

noncomputable def value (S Q : Source) : List Bool → List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value (IntegerPolynomialSampleInput.input S) (test S Q)

theorem evaluator {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (value S Q) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator (IntegerPolynomialSampleInput.access A) (testAccess S B)

theorem packet (S Q : Source) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) c w) :
    value S Q (pair (pair c w) d) = InfinitesimalSign.encode (SignType.sign
      ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ)
        ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val (0 : Fin 1)))) := by
  rw [value, SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w d hw]
  exact congrArg (fun z : ℝ => InfinitesimalSign.encode (SignType.sign z))
    (DiagonalUnivariateSystem.eval (Q.polynomial (pair c d)) (0 : Fin 1) (Int.castRingHom ℝ)
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val)

theorem mem_PSPACE {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) (s : SignType) :
    SquareSampleCompleteIndexedPolynomialTest.language (IntegerPolynomialSampleInput.input S) (test S Q) s ∈ PSPACE :=
  SquareSampleCompleteIndexedPolynomialTest.mem_PSPACE (IntegerPolynomialSampleInput.access A) (testAccess S B) s

end LeanCanny.Encoding.IntegerPolynomialIndexedSampleTest
