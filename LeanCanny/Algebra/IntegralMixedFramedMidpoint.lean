/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialMidpointSpace
public import LeanCanny.Algebra.IntegralMixedFramedWindowQuery
/-! # Two actual retained cofactors give a midpoint without a new birth -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedMidpoint
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open RationalSubstitution.IntegerBits (context context_mem_FP selectedDegree selectedDegree_mem_FP)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (left right : List Bool→ℕ)

noncomputable def family : RationalMonomialMidpoint.Family where
  arity q:=(atKey P D H (key q)).count
  leftIndex:=left
  rightIndex:=right
  leftWeight:=(IntegralMixedFramedWindowQuery.family P D H L F C hs key left).weight
  rightWeight:=(IntegralMixedFramedWindowQuery.family P D H L F C hs key right).weight
  left:=IntegralMixedFramedBankScalars.scalars P D H L F C hs key left
  right:=IntegralMixedFramedBankScalars.scalars P D H L F C hs key right
  sameDenominator _:=rfl

noncomputable def coefficient (W : List Bool→ℕ) :=
  FixedWidthRowBits.value (fun q=>(atKey P D H (key (context q))).count) (W ∘ context)
    (fun q=>RationalMonomialMidpoint.numerator (family P D H L F C hs key left right) (context q))
    selectedDegree pairSnd

noncomputable def denominator (q : List Bool) :=residueBits
  (RationalMonomialMidpoint.denominator (family P D H L F C hs key left right) (context q) :
    ZMod (Nat.fromBitsLE (pairSnd q)+1))

theorem native (a : Access P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hk : key∈FP) (hl : BinaryFn left) (hr : BinaryFn right)
    (W : List Bool→ℕ) (hW : UnaryFn W) :
    SpaceFunction (coefficient P D H L F C hs key left right W) ∧
      SpaceFunction (denominator P D H L F C hs key left right) :=by
  let MF:=family P D H L F C hs key left right
  have AL:=IntegralMixedFramedBankScalars.access P a D H Hnew c hb hL hF hC hs hk hl
  have AR:=IntegralMixedFramedBankScalars.access P a D H Hnew c hb hL hF hC hs hk hr
  have EL:=RationalMonomialMidpoint.scalar_residue_evaluator MF.left AL true
  have ER:=RationalMonomialMidpoint.scalar_residue_evaluator MF.right AR true
  have ED:=RationalMonomialMidpoint.scalar_residue_evaluator MF.left AL false
  have HA : UnaryFn MF.arity:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp hk
  have WL : BinaryFn MF.leftWeight:=IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs key left a hk hl
  have WR : BinaryFn MF.rightWeight:=IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs key right a hk hr
  constructor
  · exact RationalMonomialMidpoint.coefficient_evaluator (RationalMonomialMidpoint.pull MF context) (W ∘ context)
      selectedDegree pairSnd (HA.comp context_mem_FP) (hW.comp context_mem_FP)
      (hl.comp context_mem_FP) (hr.comp context_mem_FP) (WL.comp context_mem_FP) (WR.comp context_mem_FP)
      selectedDegree_mem_FP pairSnd_mem_FP EL ER
  · exact RationalMonomialMidpoint.denominator_evaluator (RationalMonomialMidpoint.pull MF context)
      pairSnd pairSnd_mem_FP ED

end LeanCanny.Algebra.IntegralMixedFramedMidpoint
