/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankTermSpace
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
/-! # Native multivariate term tests over an implicit current-Q integer bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankTermCurrentQ
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (B : Bank)
noncomputable def test (word : List Bool→List Bool) : SquareSampleCompleteIndexedPolynomialTest.Test (IntegralFramedBankQuery.input B) where
  polynomial c _:=IntegralMixedFramedBankTermBits.polynomial B.parameters B.plan B.data word (B.key c)
  degree z:=IntegralMixedFramedBankTermBits.degree B.parameters B.plan B.data word (B.key (pairFst z))
  mass z:=IntegralMixedFramedBankTermBits.mass B.parameters B.plan B.data word B.nodes B.factor B.seed (B.key (pairFst z))
  polynomial_degree z:=IntegralMixedFramedBankTermBits.polynomial_degree B.parameters B.plan B.data word (B.key (pairFst z))
  polynomial_mass z:=IntegralMixedFramedBankTermBits.polynomial_mass B.parameters B.plan B.data word B.nodes B.factor B.seed B.bounds (B.key (pairFst z))

def coefficientQuery (key : List Bool→List Bool) (q : List Bool) := pair
  (pair (key (pairFst (RationalSubstitution.IntegerBits.context q))) (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
theorem coefficientQuery_FP {key : List Bool→List Bool} (hk : key∈FP) : coefficientQuery key∈FP:=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP) hk)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem coefficient_eq (word : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedBankTermBits.coefficient B.parameters B.plan B.data word (coefficientQuery B.key q)=
      SquareSampleCompleteIndexedPolynomialTest.coefficient (test B word) q := by
  unfold coefficientQuery
  rw [IntegralMixedFramedBankTermBits.coefficient_std,FixedWidthPolynomial.nativeExponent_refl]
  rfl

theorem test_access (h : IntegralFramedBankQuery.Access B) (word : List Bool→List Bool) (hw : word∈FP) : (test B word).Access where
  degree:=(IntegralMixedFramedBankTermBits.degree_binary B.parameters h.parameters B.plan B.data word hw).comp (mem_FP_comp pairFst_mem_FP h.key)
  mass:=(IntegralMixedFramedBankTermBits.mass_binary B.parameters h.parameters B.plan B.data word hw h.nodes h.factor h.seed).comp (mem_FP_comp pairFst_mem_FP h.key)
  coefficient:=((IntegralMixedFramedCurrentQBankTermBits.coefficient_evaluator B.parameters h.parameters B.plan B.data
    h.liftedData h.controls h.bounds word hw).precompose (coefficientQuery B.key) (coefficientQuery_FP h.key)).congr
      (funext fun q=>coefficient_eq B word q)

noncomputable def value (word : List Bool→List Bool) : List Bool→List Bool :=
  SquareSampleCompleteIndexedPolynomialTest.value (IntegralFramedBankQuery.input B) (test B word)

theorem evaluator (h : IntegralFramedBankQuery.Access B) (word : List Bool→List Bool) (hw : word∈FP) :
    SpaceFunction (value B word) :=
  SquareSampleCompleteIndexedPolynomialTest.evaluator (IntegralFramedBankQuery.input_access B h) (test_access B h word hw)

noncomputable def point (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input B) c w) : ℕ→ℝ :=
  LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point B.parameters B.plan B.data (B.key c)
    (SquareSampleCompleteVertices.candidate (IntegralFramedBankQuery.input B) c w hv).val

theorem packet (word : List Bool→List Bool) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedBankQuery.input B) c w) :
    value B word (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (B.key c)).eval (point B c w hv))) := by
  rw [value,SquareSampleCompleteIndexedPolynomialTest.packet _ _ c w d hv]
  exact congrArg InfinitesimalSign.encode (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.sign
    B.parameters B.plan B.data word (B.key c) _)

end LeanCanny.Encoding.IntegralFramedBankTermCurrentQ
