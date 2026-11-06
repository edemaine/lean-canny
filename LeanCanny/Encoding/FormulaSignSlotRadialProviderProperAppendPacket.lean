/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordReceipt
/-! # The general proper word uses its exact prepared provider context -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth initial)

theorem root_packet (old : List Bool) (l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.root (packet (dimension old) old l r side w)=preparedRoot old l r side := by
  unfold preparedRoot
  simp only [FormulaSignSlotRadialProviderAtomic.root,provider_packet,payload_packet]

theorem context_packet (old : List Bool) (l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.context (packet (dimension old) old l r side w)=
      FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old l r side) := by
  simp only [FormulaSignSlotRadialProviderAtomic.context,root_packet,
    FormulaSignSlotRadialProviderRecordPrefix.context]

theorem sample_query_packet (old : List Bool) (l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.sampleQuery (packet (dimension old) old l r side w)=
      LeanCanny.pair (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old l r side)) w := by
  rw [FormulaSignSlotRadialProviderAtomic.sampleQuery,context_packet,word_packet]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem WordReceipt.full_valid
    {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
    {hd : depth old<dimension old} {left right : ParentEndpoint old hv hd}
    {R : CanonicalPair old hv hd left right} {side : Bool} {z : ℕ→ℝ}
    {p0 : Fin (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient
      (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ}
    (W : WordReceipt old hv hd left right R side z p0) :
    FormulaSignSlotRadialProviderAtomic.FullValid (packet (dimension old) old R.leftSpec R.rightSpec side W.word) := by
  simpa only [FormulaSignSlotRadialProviderAtomic.FullValid,context_packet,word_packet,
    FormulaSignSlotRadialProviderAtomic.input,FormulaSignSlotRadialProviderRecordPrefix.context,
    WordReceipt.word] using W.valid

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
