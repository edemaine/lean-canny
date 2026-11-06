/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPacket
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPastValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderReplayRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedRetention
/-! # The fresh own retained word preserves the actual marked and replay gates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem initial_number (old : List Bool) :
    N old=FormulaSignSlotRadialExternalContext.number (FormulaSignSlotRadialProviderAtomic.provider old)+8 := by
  rw [FormulaSignSlotRadialProviderAtomic.initial_provider]
  rfl

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.old_fields (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb : b<N old+start old) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=
      FormulaSignSlotRadialProviderAtomic.field old hv b :=
  past_fields old hv hd e he W.word W.valid W.old_raw_native b hb

theorem WordReceipt.marked (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.Marked.Holds (packet (dimension old) old e W.word) := by
  apply FormulaSignSlotRadialProviderAtomic.marked_of_initial_fields old hv _ W.full_valid
    (provider_packet _ _ _ _)
  intro i hi
  change i<FormulaSignSlotRadialExternalContext.number (FormulaSignSlotRadialProviderAtomic.provider old)+8 at hi
  have HI : i<N old+start old := by
    have H := initial_number old
    omega
  simpa only [context_packet,word_packet] using W.old_fields i HI

theorem WordReceipt.replay (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.Replay (packet (dimension old) old e W.word) := by
  apply FormulaSignSlotRadialProviderAtomic.replay_of_initial_fields old hv _ W.full_valid
    (provider_packet _ _ _ _)
  intro i hi
  have HI : i<N old+start old := by
    have H := initial_number old
    omega
  simpa only [context_packet,word_packet] using (W.old_fields i HI).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
