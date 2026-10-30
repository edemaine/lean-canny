/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Algebra.UnivariateRowSpace

/-! # Native univariate tests on any coordinate of a complete root

The indexed integer polynomial and coordinate are read from query fields,
while the original complete source and label stay fixed.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open SquareSampleInput (Inputs)
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def normalize (z : List Bool) : List Bool := pair (pairFst z) (pairSnd z)
theorem normalize_FP : normalize ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def test (F : Inputs) (Q : Source) (coordinate : (c d : List Bool) → Fin (F.count c)) :
    SquareSampleCompleteIndexedPolynomialTest.Test F where
  polynomial c d := (Q.polynomial (pair c d)).toMvPolynomial (coordinate c d)
  degree z := Q.degree (normalize z)
  mass z := Q.mass (normalize z)
  polynomial_degree z := (DiagonalUnivariateSystem.degree_le _ _).trans (Q.degree_bound (normalize z))
  polynomial_mass z := (DiagonalUnivariateSystem.mass_le _ _).trans (Q.mass_bound (normalize z))

theorem testAccess {F : Inputs} (h : F.Access) {Q : Source} (A : IntegerPolynomialRootQueriesBits.Access Q)
    (coordinate : (c d : List Bool) → Fin (F.count c))
    (hi : UnaryFn (fun z => (coordinate (pairFst z) (pairSnd z)).val)) : (test F Q coordinate).Access := by
  have hc := RationalSubstitution.IntegerBits.context_mem_FP
  have hD : BinaryFn (Q.degree ∘ normalize) := A.degree.comp normalize_FP
  have hW : UnaryFn (fun z => (Q.degree (normalize z)).size) :=
    (UnaryFn.length hD.bits_mem_FP).of_eq (fun z => BinaryNatCode.length_encode _)
  have P := PolynomialFamilyProductBits.reindexEvaluator A.coefficient (normalize ∘ RationalSubstitution.IntegerBits.context)
    (mem_FP_comp hc normalize_FP)
  have E := UnivariateRowBits.evaluator (h.count.comp (mem_FP_comp hc pairFst_mem_FP)) (hW.comp hc)
    (fun q => coordinate (pairFst (RationalSubstitution.IntegerBits.context q))
      (pairSnd (RationalSubstitution.IntegerBits.context q))) (hi.comp hc)
    (Q.polynomial ∘ normalize ∘ RationalSubstitution.IntegerBits.context) P
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨hD, A.mass.comp normalize_FP, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

noncomputable def value (F : Inputs) (Q : Source) (coordinate : (c d : List Bool) → Fin (F.count c)) : List Bool → List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value F (test F Q coordinate)

theorem evaluator {F : Inputs} (h : F.Access) {Q : Source} (A : IntegerPolynomialRootQueriesBits.Access Q)
    (coordinate : (c d : List Bool) → Fin (F.count c))
    (hi : UnaryFn (fun z => (coordinate (pairFst z) (pairSnd z)).val)) : SpaceFunction (value F Q coordinate) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator h (testAccess h A coordinate hi)

theorem packet (F : Inputs) (Q : Source) (coordinate : (c d : List Bool) → Fin (F.count c)) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) :
    value F Q coordinate (pair (pair c w) d) = InfinitesimalSign.encode (SignType.sign
      ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ)
        ((SquareSampleCompleteVertices.candidate F c w hw).val (coordinate c d)))) := by
  rw [value, SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w d hw]
  exact congrArg (fun z : ℝ => InfinitesimalSign.encode (SignType.sign z))
    (DiagonalUnivariateSystem.eval _ _ _ _)

end LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
