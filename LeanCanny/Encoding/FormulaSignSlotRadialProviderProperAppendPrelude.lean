/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSampledLevel
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPacket
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedRetention
/-! # Every sampled proper child retains its actual marked and provider replay gates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem initial_number (old : List Bool) :
    N old=FormulaSignSlotRadialExternalContext.number (FormulaSignSlotRadialProviderAtomic.provider old)+8 := by
  rw [FormulaSignSlotRadialProviderAtomic.initial_provider]
  rfl

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}

theorem SampledLevel.old_fields (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb : b<N old+start old) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side))
      S.receipt.word S.receipt.valid b=FormulaSignSlotRadialProviderAtomic.field old hv b :=
  past_fields old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)
    S.receipt.word S.receipt.valid (S.receipt.old_raw_native S.old_raw) b hb

theorem SampledLevel.marked (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.Marked.Holds
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) := by
  apply FormulaSignSlotRadialProviderAtomic.marked_of_initial_fields old hv _ S.receipt.full_valid
    (provider_packet _ _ _ _ _ _)
  intro i hi
  change i<FormulaSignSlotRadialExternalContext.number (FormulaSignSlotRadialProviderAtomic.provider old)+8 at hi
  have HI : i<N old+start old := by have H := initial_number old;omega
  simpa only [context_packet,word_packet] using S.old_fields i HI

theorem SampledLevel.replay (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.Replay
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) := by
  apply FormulaSignSlotRadialProviderAtomic.replay_of_initial_fields old hv _ S.receipt.full_valid
    (provider_packet _ _ _ _ _ _)
  intro i hi
  have HI : i<N old+start old := by have H := initial_number old;omega
  simpa only [context_packet,word_packet] using (S.old_fields i HI).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
