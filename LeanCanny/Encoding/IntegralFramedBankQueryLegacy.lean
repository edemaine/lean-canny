/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Algebra.IntegralMixedFramedBankScalarsOriginal

/-! # Actual original-bank queries include their own native planning

All original syntax costs are discharged by the existing original controller.
Its normalization and arbitrary-modulus pullbacks stay inside the proof.
The queried bank and complete candidate retain their original parameters.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankQueryLegacy
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
set_option backward.isDefEq.respectTransparency false

variable (B : Bank) (a : IntegralCriticalHistoryTask.Access B.parameters)
  (s : IntegralMixedFramedNativeBits.Syntax B.parameters B.plan B.data)
  (hs : IntegralMixedFramedStepHeight.FamilyInputs B.parameters B.plan s.nodes s.factor s.seed)
  (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
  (hLB : BinaryFn B.nodes) (hFB : BinaryFn B.factor) (hCB : BinaryFn B.seed)
  (hk : B.key∈FP) (hi : UnaryFn (fun c=>(B.coordinate c).val))

include a s hs hF hL hLB hFB hCB hk

theorem input_access : (IntegralFramedBankQuery.input B).Access :=
  IntegralFramedCompleteSquare.access B.parameters a B.plan B.data B.nodes B.factor B.seed B.bounds hLB hFB hCB
    B.key hk B.positive
    (IntegralFramedCompleteSquare.row_evaluator B.parameters a B.plan B.data B.nodes B.factor B.seed B.bounds B.key hk B.positive
      (IntegralMixedFramedCompanionUniformBits.original_evaluator B.parameters a B.plan B.data s hs hF hL))

include hi

theorem evaluator (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceFunction (IntegralFramedBankQuery.value B Q) := by
  have HK : IntegralFramedBankUnivariateTest.saved B.key∈FP:=mem_FP_comp pairFst_mem_FP hk
  have HI : UnaryFn (IntegralFramedBankUnivariateTest.selected (fun c _=>B.coordinate c)):=hi.comp pairFst_mem_FP
  have HA:=IntegralMixedFramedBankScalarsOriginal.access B.parameters a B.plan B.data s hs hF hL
    hLB hFB hCB B.bounds HK (BinaryFn.ofUnary HI)
  have HP:=IntegralMixedFramedBankUnivariateSource.power_binary B.parameters a B.plan B.data HK HI
  have HT : IntegerPolynomialRootQueriesBits.Access
      (IntegralFramedBankUnivariateTest.source B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key
        (fun c _=>B.coordinate c) Q) :=
    IntegerPolynomialRationalPointSource.access Q hQ _ HA HP (fun _=>UniformIntegralPowerSchedule.birth_pos _ _ _)
  exact SquareSampleCompleteUnivariateTest.evaluator (input_access B a s hs hF hL hLB hFB hCB hk)
    HT (fun c _=>B.coordinate c) HI

end LeanCanny.Encoding.IntegralFramedBankQueryLegacy
