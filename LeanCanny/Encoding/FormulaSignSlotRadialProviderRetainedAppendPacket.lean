/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordReceipt
/-! # The retained own word uses its exact prepared provider context -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth initial)

theorem root_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.root (packet (dimension old) old e w)=preparedRoot old e := by
  unfold preparedRoot
  simp only [FormulaSignSlotRadialProviderAtomic.root,provider_packet,payload_packet]

theorem context_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.context (packet (dimension old) old e w)=
      FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e) := by
  simp only [FormulaSignSlotRadialProviderAtomic.context,root_packet,
    FormulaSignSlotRadialProviderRecordPrefix.context]

theorem sample_query_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.sampleQuery (packet (dimension old) old e w)=
      LeanCanny.pair (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)) w := by
  rw [FormulaSignSlotRadialProviderAtomic.sampleQuery,context_packet,word_packet]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem WordReceipt.full_valid
    {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
    {hd : depth old<dimension old} {e : ℕ} {he : e<endBirth (dimension old) (initial old) old}
    {p : Fin (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (preparedRoot old e)+1)→ℝ}
    (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.FullValid (packet (dimension old) old e W.word) := by
  simpa only [FormulaSignSlotRadialProviderAtomic.FullValid,context_packet,word_packet] using W.valid

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
