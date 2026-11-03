/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
/-! # Native space for ordered actual principal signs on one full vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleCompleteIndexedPolynomialTest.value
  SquareSampleCompleteSuffixPolynomialTest.test FixedWidthTarskiPrincipalBits.polynomial

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (j budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b))).totalDegree≤budget (pair c b))
variable (hmass : ∀c b,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) (j (pair c b)))≤2^height (pair c b))
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

variable (T : IntegralMixedHeaderTablesBits.Tables) (hrT : IntegralMixedFramedHeaderBits.Represents P D H T)
variable (a : Access P) (hT : IntegralMixedHeaderTablesBits.Access T) (hk : key∈FP)
variable (hS : (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos).Access) (A : FixedWidthTarskiPrincipalBits.Access MF) (hW : UnaryFn MF.width)
variable (hr : read∈FP) (hj : BinaryFn j) (hD : BinaryFn budget) (hH : BinaryFn height)
variable (hfit : ∀c b,budget (pair c b)<2^MF.width (read (pair c b)))
include hrT a hT hk hS A hW hr hj hD hH hfit in
theorem source_access :
    (source P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass).Access :=by
  unfold source
  apply IntegralFramedScalarEmbeddedTarskiParameterTest.access P D H L F C hs key hpos O hc
    MF (read∘base) (j∘base) delta epsilon (budget∘base) (height∘base) _ _ _ T hrT a hT hk hS.count
    A hW (mem_FP_comp base_FP hr) (hj.comp base_FP) delta_binary epsilon_binary
    (hD.comp base_FP) (hH.comp base_FP)
  intro c b
  simpa only [Function.comp_apply,base,pairFst_pair,pairSnd_pair] using hfit c (pairFst (pairFst b))

include hrT a hT hk hS A hW hr hj hD hH hfit in
theorem coefficient_evaluator :
    SpaceFunction (coefficientSign P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass) :=by
  have E:=SquareSampleCompleteSuffixPolynomialTest.evaluator hS _
    (source_access P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass
      T hrT a hT hk hS A hW hr hj hD hH hfit)
  exact ((E.precompose query query_FP).postcompose (fun w=>w.take 2)
    (take_mem_FP id_mem_FP (UnaryFn.const 2))).congr rfl

include hrT a hT hk hS A hW hr hj hD hH hfit in
theorem evaluator :
    SpaceFunction (value P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass) :=
  RealIteratedInfinitesimalSignSpace.evaluator
    (coefficient_evaluator P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass
      T hrT a hT hk hS A hW hr hj hD hH hfit)
    (coefficient_length P D H L F C hs key hpos O hc MF read j budget height dim hdegree hmass)
    (budget∘inputContext) (budget∘inputContext) (hD.comp inputContext_FP) (hD.comp inputContext_FP)

end LeanCanny.Encoding.IntegralFramedScalarTarskiIteratedSign
