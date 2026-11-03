/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalUnivariateTest
/-! # Original native costs for full-physical integer-leaf queries

Only the original integer Source.Access and the literal full-system row
backend are charged. Bank denominators/cofactors are computed by the
verified arbitrary-modulus current-Q controller, with no inverse residue.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalUnivariateTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedHeaderTablesBits.Access T)
  (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (hk : key∈FP)
  (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c)))
  (hi : UnaryFn (selected P D H key coordinate))

include a hT hr hk hi in
theorem column_unary : UnaryFn (fun z=>(column P D H key coordinate (pairFst z) (pairSnd z)).val) := by
  have E : UnaryFn (fun z=>IntegralMixedFramedPhysicalIndex.scalarColumn P T
      (pair (key (pairFst z)) (BinaryNatCode.encode (selected P D H key coordinate z)))) :=
    (IntegralMixedFramedPhysicalIndex.scalarColumn_unary P a T hT).comp
      (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) (BinaryFn.ofUnary hi).bits_mem_FP)
  exact E.of_eq (fun z=>IntegralMixedFramedPhysicalIndex.scalarColumn_actual P D H T hr
    (key (pairFst z)) (coordinate (pairFst z) (pairSnd z)))

variable (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
  (nc : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew nc)
  {L F C : List Bool→ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q)

include a hk hi hL hF hC hb hQ in
theorem source_access : IntegerPolynomialRootQueriesBits.Access
    (source P D H L F C hs key coordinate Q) :=
  IntegralMixedFramedBankUnivariateSource.access P a D H Hnew nc hb hL hF hC hs
    (mem_FP_comp pairFst_mem_FP hk) hi Q hQ

include a hT hr hk hi hL hF hC hb hQ in
theorem evaluator (hpos : ∀c,0<(family P D H).birth (key c))
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos))) :
    SpaceFunction (value P D H L F C hs key hpos coordinate Q) :=
  SquareSampleCompleteUnivariateTest.evaluator
    (IntegralFramedPhysicalSquare.access P a D H T hT hr L F C hs hL hF hC key hk hpos ER)
    (source_access P a D H key hk coordinate hi Hnew nc hb hL hF hC hs Q hQ)
    (column P D H key coordinate) (column_unary P a D H T hT hr key hk coordinate hi)

end LeanCanny.Encoding.IntegralFramedPhysicalUnivariateTest
