/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateRootSource
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQOldHeightSpace
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQBankProducts

/-! # Retained-coordinate annihilators from the original current-Q backend

Both the actual cleared multiplication matrix and its common denominator are
computed from original controls. Integer leaves need no serialized term word.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (a : Access P) (D : Plan P)
  (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D)
    (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D)
    (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) c)

include a c hb in
theorem currentQ_entry_space : SpaceFunction (access P a D H).entry :=
  (IntegralMixedFramedOldHeightQueryBits.currentQ_evaluator P a D H c hb).precompose
    entryPacket entryPacket_FP

include a c hb in
theorem currentQ_common_space : SpaceFunction (fun z => residueBits
    (common P D H (context z) : ZMod ((characteristic P D H).modulus z))) := by
  have E := (IntegralMixedFramedCurrentQBankProductBits.common_evaluator P a D H _ c hb).precompose
    commonPacket commonPacket_FP
  have HB (z : List Bool) : PaddedIntegralGeneratorSource.base (commonPacket z)=key (context z) := by
    simp only [commonPacket,PaddedIntegralGeneratorSource.base,pairFst_pair]
  have HM (z : List Bool) : IntegralMixedFramedCompanionQueryBits.callerModulus (commonPacket z)=
      (characteristic P D H).modulus z := by
    simp only [commonPacket,IntegralMixedFramedCompanionQueryBits.callerModulus,
      PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
    rfl
  exact E.congr (funext fun z => congrArg₂
    (fun (k : List Bool) (m : ℕ) => residueBits (IntegralMixedHistory.commonDenominator ((family P D H).state k) : ZMod m))
      (HB z) (HM z))

include a c hb in
theorem currentQ_coefficient_space :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial P D H)) :=
  (IntegralScaledCharacteristicBits.evaluator (characteristic P D H) (access P a D H)
    (fun z => common P D H (context z)) (fun _ => 1) (BinaryFn.const 1)
    (currentQ_entry_space P a D H c hb) (currentQ_common_space P a D H c hb)).congr
      (funext fun z => scaled_value P D H z)

include a c hb in
theorem currentQ_rootAccess (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegerPolynomialRootQueriesBits.Access (rootSource P D H L F C hs) where
  coefficient := currentQ_coefficient_space P a D H c hb
  degree := dimension_binary P a D H
  mass := massBound_binary P a D H hL hF hC

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
