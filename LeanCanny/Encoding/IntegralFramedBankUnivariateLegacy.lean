/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankUnivariateTest
public import LeanCanny.Algebra.IntegralMixedFramedBankScalarsOriginal

/-! # Original-bank tests with coordinate selection in the query datum

The complete source and label stay literal. Coordinate and derivative
selection can vary in the query datum, with original planning performed
inside the existing original coefficient backend.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankUnivariateLegacy
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
set_option backward.isDefEq.respectTransparency false

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    {L F C : List Bool→ℕ} (hLB : BinaryFn L) (hFB : BinaryFn F) (hCB : BinaryFn C)
    (hB : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀ c,0<(atKey P D H (key c)).count)
    (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count)
    (hi : UnaryFn (IntegralFramedBankUnivariateTest.selected coordinate))
    (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceFunction (IntegralFramedBankUnivariateTest.value P D H L F C hB key hpos coordinate Q) := by
  have HK : IntegralFramedBankUnivariateTest.saved key∈FP:=mem_FP_comp pairFst_mem_FP hk
  have HA:=IntegralMixedFramedBankScalarsOriginal.access P a D H s hs hF hL hLB hFB hCB hB HK (BinaryFn.ofUnary hi)
  have HP:=IntegralMixedFramedBankUnivariateSource.power_binary P a D H HK hi
  have HT : IntegerPolynomialRootQueriesBits.Access
      (IntegralFramedBankUnivariateTest.source P D H L F C hB key coordinate Q) :=
    IntegerPolynomialRationalPointSource.access Q hQ _ HA HP (fun _=>UniformIntegralPowerSchedule.birth_pos _ _ _)
  have HF:=(IntegralFramedCompleteSquare.access P a D H L F C hB hLB hFB hCB key hk hpos
    (IntegralFramedCompleteSquare.row_evaluator P a D H L F C hB key hk hpos
      (IntegralMixedFramedCompanionUniformBits.original_evaluator P a D H s hs hF hL)))
  exact SquareSampleCompleteUnivariateTest.evaluator HF HT coordinate hi

end LeanCanny.Encoding.IntegralFramedBankUnivariateLegacy
