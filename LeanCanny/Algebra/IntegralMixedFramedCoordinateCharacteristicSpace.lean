/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicSource
/-! # Original syntax evaluates old cleared-coordinate characteristic coefficients

Both the old matrix entries and the common denominator are computed by charged
native controllers from the same original script. The coefficient caller keeps
its full saved key and arbitrary modulus; no interpreted matrix reader is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Request the same old prefix and modulus from the streamed bank product. -/
def commonPacket (z : List Bool) := pair (pair (key (context z)) (pairSnd z)) []

theorem commonPacket_FP : commonPacket ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
    pairSnd_mem_FP) (constFn_mem_FP [])

theorem entry_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1 ≤ s.factor root) (hL : ∀ root, 1 ≤ s.nodes root) :
    SpaceFunction (access P a D H).entry :=
  (IntegralMixedFramedOldHeightQueryBits.evaluator P a D H s hs hF hL).precompose entryPacket entryPacket_FP

theorem common_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1 ≤ s.factor root) (hL : ∀ root, 1 ≤ s.nodes root) :
    SpaceFunction (fun z => residueBits (common P D H (context z) : ZMod ((characteristic P D H).modulus z))) := by
  have E := (IntegralMixedFramedBankProductBits.common_evaluator P a D H s hs hF hL).precompose commonPacket commonPacket_FP
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

theorem coefficient_space (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root, 1 ≤ s.factor root) (hL : ∀ root, 1 ≤ s.nodes root) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial P D H)) := by
  exact (IntegralScaledCharacteristicBits.evaluator (characteristic P D H) (access P a D H)
    (fun z => common P D H (context z)) (fun _ => 1) (BinaryFn.const 1)
    (entry_space P a D H s hs hF hL) (common_space P a D H s hs hF hL)).congr
      (funext fun z => scaled_value P D H z)

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
