/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNativeMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
/-! # The actual completed seed history has no creating cut stage -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "ROOT" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedRootPullback.instructionAt stageHeader
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

theorem no_cut_at (old : List Bool) (b : ℕ)
    (hb : b<number n (ROOT old)+8+IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    ¬IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D (ROOT old) b).command :=by
  intro HC
  have HE:=(IntegralFramedCreatingCut.isCut_iff_context _).mp HC
  rw [←IntegralMixedCommandHeaderBits.command_context] at HE
  have HH : stageHeader hn ht ha hR0 (ROOT old) b=
      IntegralMixedCommandHeaderBits.command (IntegralMixedFramedRootPullback.instructionAt P D (ROOT old) b).command:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank stageHeader
    rfl
  rw [←HH] at HE
  by_cases hi : b<number n (ROOT old)+8
  · rw [prelude_header hn ht ha hR0 _ _ hi] at HE
    exact (by omega : ¬2≤0) HE
  · have HL : b=number n (ROOT old)+8+(b-(number n (ROOT old)+8)):=by omega
    rw [HL,seed_header hn ht ha hR0 old _ (by omega)] at HE
    exact (by omega : ¬2≤1) HE

theorem before_probe_holds (old w : List Bool) :
    IntegralMixedPhysicalTraceBeforeProbe.holds hn ht ha (radius_binary hR0) false (pair (ROOT old) w) :=by
  intro j hj HC
  have HL:=IntegralMixedPhysicalTraceCutScan.count_eq_length hn ht ha (radius_binary hR0) false (ROOT old) w
  have HJ : j<IntegralFramedTraceCutMetadata.length P D (ROOT old)+1:=by omega
  have Hcut:=(IntegralFramedTraceCutOrigin.stageCut_iff P D (pair (ROOT old) w) j
    (by simpa only [pairFst_pair] using HJ)).mp HC
  have HValues :=IntegralMixedPhysicalTraceCutValidity.birth_count hn ht ha (radius_binary hR0) false (ROOT old) w
  have HCount : IntegralMixedPhysicalTraceCutScan.count hn ht ha (radius_binary hR0) false (pair (ROOT old) w)=
      number n (ROOT old)+8+IntegralMixedCausalRecordPlanBits.count (ROOT old):=by
    exact HValues.symm.trans ((IntegralMixedFramedHistoryFamilyBits.family_birth P D
      (IntegralFramedBankQuery.Bank.data B) ((B).key (context hn ht ha hR0 old))).trans
        (prefix_length hn ht ha hR0 old))
  have HB : j<number n (ROOT old)+8+IntegralMixedCausalRecordPlanBits.count (ROOT old):=by omega
  rw [pairFst_pair] at Hcut
  exact False.elim (no_cut_at hn ht ha hR0 old j HB Hcut)

end LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
