/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQLeadingPlannedSpace
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot

/-! # Streamed bank products with a native integer-polynomial backend

Creating leading residues come from the verified current-Q machine. This
supports integer annihilator leaves without requiring serialized term words.
Every product keeps the caller modulus and its original saved source.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProductPlannedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedCurrentQCompanionPlannedBits (parameters plan data)
open scoped Classical

variable (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
  (L F C : List Bool → ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
  (c : IntegralMixedFramedCurrentQNativeBits.Controls (parameters P L F C) (plan P D L F C) (data P D Hnew L F C))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (parameters P L F C) (plan P D L F C) (data P D Hnew L F C) c)
include a Hnew L F C hL hF hC c hb

theorem denominator_evaluator : SpaceFunction (IntegralMixedFramedBankDenominatorBits.value P D H) := by
  have EL:=IntegralMixedFramedCurrentQLeadingPlannedBits.evaluator P a D H Hnew L F C hL hF hC c hb
  have EE:=EL.call (IntegralMixedFramedBankDenominatorBits.creatorPacket P D H)
    (IntegralMixedFramedBankDenominatorBits.finish P D H)
    (IntegralMixedFramedBankDenominatorBits.creatorPacket_FP P a D H)
    (IntegralMixedFramedBankDenominatorBits.finish_FP P a D H)
  exact EE.congr (funext fun q=>by
    simp only [IntegralMixedFramedBankDenominatorBits.finish,pairFst_pair,pairSnd_pair]
    split_ifs with hi
    · exact IntegralMixedFramedBankDenominatorBits.creator_value P D H q hi
    · unfold IntegralMixedFramedBankDenominatorBits.value IntegralMixedFramedBankDenominatorBits.integerAt
      rw [dite_eq_right hi]
      exact ArithmeticBits.zero_residueBits _)

theorem factor_evaluator (skip : List Bool→ℕ) (hk : BinaryFn skip) :
    SpaceFunction (IntegralMixedFramedBankProductBits.factor P D H skip) := by
  have ED:=denominator_evaluator P a D H Hnew L F C hL hF hC c hb
  have EO:=(SpaceFunction.ofFP _ IntegralMixedFramedLeadingBits.defaultValue_FP).precompose pairFst pairFst_mem_FP
  have HG:=(BinaryFn.fromBits pairSnd_mem_FP).eq (hk.comp pairFst_mem_FP)
  exact (SpaceFunction.branch _ HG.flag_mem_FP EO
    (ED.precompose IntegralMixedFramedBankProductBits.factorPacket IntegralMixedFramedBankProductBits.factorPacket_FP)).congr
      (funext fun z=>by simp only [IntegralMixedFramedBankProductBits.factor,decide_eq_true_eq,Function.comp_apply])

theorem evaluator (skip : List Bool→ℕ) (hk : BinaryFn skip) :
    SpaceFunction (IntegralMixedFramedBankProductBits.value P D H skip) := by
  have HN:=BinaryFn.ofUnary (IntegralMixedFramedBankDenominatorBits.count_unary P a D H)
  have HM:=IntegralMixedFramedCompanionQueryBits.callerModulus_binary.bits_mem_FP
  have EE:=ModularProduct.evaluatorWithModulus (factor_evaluator P a D H Hnew L F C hL hF hC c hb skip hk)
    (fun q=>BinaryNatCode.encode (IntegralMixedFramedBankDenominatorBits.count P D H q))
    (fun q=>BinaryNatCode.encode (IntegralMixedFramedCompanionQueryBits.callerModulus q)) HN.bits_mem_FP HM
    IntegralMixedFramedCompanionQueryBits.callerModulus
    (funext fun q=>Nat.fromBitsLE_bits _)
    (fun q i=>((if i=skip q then 1 else IntegralMixedFramedBankDenominatorBits.integerAt P D H q i : ℤ) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
    (fun q=>by unfold IntegralMixedFramedCompanionQueryBits.callerModulus; omega)
    (fun q i _=>IntegralMixedFramedBankProductBits.factor_packet P D H skip q i)
  exact EE.congr (funext fun q=>by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedFramedBankProductBits.value,
      IntegralMixedFramedBankProductBits.integer,Int.cast_prod])

theorem common_evaluator : SpaceFunction (fun q=>residueBits
    (IntegralMixedHistory.commonDenominator (IntegralMixedFramedBankDenominatorBits.state P D H q) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
  (evaluator P a D H Hnew L F C hL hF hC c hb (IntegralMixedFramedBankDenominatorBits.count P D H)
    (BinaryFn.ofUnary (IntegralMixedFramedBankDenominatorBits.count_unary P a D H))).congr
      (funext fun q=>by unfold IntegralMixedFramedBankProductBits.value; rw [IntegralMixedFramedBankProductBits.common_integer])

end LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProductPlannedBits
