/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCurrentQSquareSpace
public import LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
public import LeanCanny.Geometry.IntegralMixedFramedBankUnivariateSign

/-! # Native implicit univariate queries at actual complete bank candidates

The complete source and candidate label remain fixed. The datum selects an
implicit integer polynomial and a retained bank coordinate. Its sign is
computed on the same raw joint tuple, with all bank scalar readers charged.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankUnivariateTest
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev input (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ q,0<(atKey P D H (key q)).count) := IntegralFramedCompleteSquare.input P D H L F C hs key hpos

def saved (key : List Bool→List Bool) (z : List Bool) := key (pairFst z)
noncomputable def selected {P : Parameters} {D : Plan P} {H : IntegralMixedFramedHistoryFamilyBits.Data P D}
    {key : List Bool→List Bool} (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count) (z : List Bool) :=
  (coordinate (pairFst z) (pairSnd z)).val

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count) (Q : IntegerPolynomialRootQueriesBits.Source) :=
  IntegralMixedFramedBankUnivariateSource.source P D H L F C hs (saved key) (selected coordinate) Q

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ q,0<(atKey P D H (key q)).count)
    (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count) (Q : IntegerPolynomialRootQueriesBits.Source) :=
  SquareSampleCompleteUnivariateTest.value (input P D H L F C hs key hpos)
    (source P D H L F C hs key coordinate Q) coordinate

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    {L F C : List Bool→ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hk : key∈FP) (hpos : ∀ q,0<(atKey P D H (key q)).count)
    (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count)
    (hi : UnaryFn (selected coordinate)) (Q : IntegerPolynomialRootQueriesBits.Source)
    (hQ : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (value P D H L F C hs key hpos coordinate Q) :=
  SquareSampleCompleteUnivariateTest.evaluator
    (IntegralFramedCurrentQSquare.access_native P a D H Hnew c hb L F C hs hL hF hC key hk hpos)
    (IntegralMixedFramedBankUnivariateSource.access P a D H Hnew c hb hL hF hC hs
      (mem_FP_comp pairFst_mem_FP hk) hi Q hQ) coordinate hi

theorem packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hpos : ∀ q,0<(atKey P D H (key q)).count)
    (coordinate : (c d : List Bool)→Fin (atKey P D H (key c)).count) (Q : IntegerPolynomialRootQueriesBits.Source)
    (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w) :
    value P D H L F C hs key hpos coordinate Q (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ)
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (key c))
          (SquareSampleCompleteVertices.candidate (input P D H L F C hs key hpos) c w hv).val (coordinate c d)))) := by
  rw [value,SquareSampleCompleteUnivariateTest.packet _ _ _ c w d hv]
  have HS:=LeanCanny.Geometry.IntegralMixedFramedBankUnivariateSign.sign P D H L F C hs
    (saved key) (selected coordinate) Q (pair c d)
  dsimp only [saved,selected] at HS
  rw [pairFst_pair,pairSnd_pair] at HS
  exact congrArg InfinitesimalSign.encode (HS _ (coordinate c d).isLt)

end LeanCanny.Encoding.IntegralFramedBankUnivariateTest
