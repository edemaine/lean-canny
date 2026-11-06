/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicFrame
public import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
public import LeanCanny.Encoding.IntegralMixedChronologicalOptionalEndpointSpec
/-! # General endpoint appends preserve the actual literal provider and resources -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def payload (d : ℕ) (old l r : List Bool) (side : Bool) :=
  IntegralMixedRoadmapChain.appendPayload d (FormulaSignSlotRadialProviderAtomic.payload old)
    l r side (IntegralMixedRoadmapChain.seedCode d)
def packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :=
  FormulaSignSlotRadialProviderAtomic.packet (FormulaSignSlotRadialProviderAtomic.provider old) (payload d old l r side) w

theorem provider_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.provider (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.provider old :=
  FormulaSignSlotRadialProviderAtomic.provider_packet _ _ _
theorem original_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.original (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.original old := by
  unfold FormulaSignSlotRadialProviderAtomic.original
  rw [provider_packet]
theorem payload_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.payload (packet d old l r side w)=payload d old l r side :=
  FormulaSignSlotRadialProviderAtomic.payload_packet _ _ _
theorem word_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.word (packet d old l r side w)=w :=
  FormulaSignSlotRadialProviderAtomic.word_packet _ _ _
theorem depth_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.depth (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.depth old+1 := by
  simp only [FormulaSignSlotRadialProviderAtomic.depth,payload_packet,payload,IntegralMixedRoadmapChain.append_depth]
theorem dimension_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.dimension (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.dimension old := by
  rw [FormulaSignSlotRadialProviderAtomic.dimension_provider,FormulaSignSlotRadialProviderAtomic.dimension_provider,provider_packet]
theorem initial_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.initial (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.initial old := by
  rw [FormulaSignSlotRadialProviderAtomic.initial_provider,FormulaSignSlotRadialProviderAtomic.initial_provider,provider_packet]
theorem width_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.width (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.width old := by
  rw [FormulaSignSlotRadialProviderAtomic.width_provider,FormulaSignSlotRadialProviderAtomic.width_provider,provider_packet]

private theorem degree_provider (q : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.parameters.degree (FormulaSignSlotRadialProviderAtomic.root q)=
      FormulaSignSlotRadialProviderIntegerPlan.parameters.degree (FormulaSignSlotRadialProviderAtomic.provider q) := by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.degree
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root q))=_
  rw [FormulaSignSlotRadialProviderAtomic.root_provider]

theorem sourceCap_packet (d : ℕ) (old l r : List Bool) (side : Bool) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.sourceCap (packet d old l r side w)=FormulaSignSlotRadialProviderAtomic.sourceCap old := by
  unfold FormulaSignSlotRadialProviderAtomic.sourceCap
  rw [dimension_packet,degree_provider,degree_provider,provider_packet]

open FormulaSignSlotRadialProviderAtomic (dimension initial width sourceCap depth frozen endBirth ownBirth)

private theorem end_birth_normalized (d N : ℕ) (old : List Bool) :
    IntegralMixedRoadmapAtomic.endBirth d N old=
      N+IntegralMixedRoadmapChain.rawStart d (FormulaSignSlotRadialProviderAtomic.payload old)
        (FormulaSignSlotRadialProviderAtomic.depth old) := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.width FormulaSignSlotRadialProviderAtomic.sourceCap
  FormulaSignSlotRadialProviderAtomic.frozen FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.payload

noncomputable def EndpointsGood (old l r : List Bool) : Prop :=
  let birth := endBirth (dimension old) (initial old) old
  IntegralMixedRoadmapEndpointSyntax.Good (dimension old) (width old) (sourceCap old) birth birth (frozen old) l ∧
    IntegralMixedRoadmapEndpointSyntax.Good (dimension old) (width old) (sourceCap old) birth
      (birth+IntegralMixedRoadmapEndpointSyntax.fresh l) (frozen old) r

theorem level_good (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    IntegralMixedRoadmapLevel.Good (dimension old) (width old) (sourceCap old)
      (endBirth (dimension old) (initial old) old) (IntegralMixedRoadmapLevel.packet (frozen old) l r side []) := by
  unfold IntegralMixedRoadmapLevel.Good
  simp only [IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
  refine ⟨?_,?_,hE.1,?_,?_,FormulaSignSlotRadialProviderAtomic.sourceCap_le old,?_⟩
  · exact IntegralMixedRoadmapLevel.frame_mono (FormulaSignSlotRadialProviderAtomic.own_frame_good old hv)
      (by unfold ownBirth;omega)
  · simpa only [IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,FormulaSignSlotRadialProviderAtomic.frozen_count]
      using Nat.succ_lt_succ hd
  · simpa only [IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.left,pairFst_pair,pairSnd_pair] using hE.2
  · cases side <;> simp only [IntegralMixedRoadmapLevel.sideWord,pairSnd_pair,pairFst_pair,
      Bool.false_eq_true,ite_false,ite_true]
    all_goals simp
  · cases side <;> simp only [IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.sideWord,
      IntegralMixedRoadmapLevel.slice,pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false,ite_true]
    all_goals rfl

theorem checked (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    IntegralMixedRoadmapChain.Checked (dimension old) (width old) (sourceCap old) (initial old) (width old)
      (payload (dimension old) old l r side) := by
  have HG := level_good old hv hd l r side hE
  have HD : IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload old)<dimension old := by
    simpa only [FormulaSignSlotRadialProviderAtomic.depth] using hd
  simp only [FormulaSignSlotRadialProviderAtomic.endBirth,end_birth_normalized,FormulaSignSlotRadialProviderAtomic.frozen,
    FormulaSignSlotRadialProviderAtomic.depth] at HG
  simpa only [payload] using IntegralMixedRoadmapChain.append_checked
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv))
    l r side (IntegralMixedRoadmapChain.seedCode (dimension old)) HD HG
    (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩).property

theorem grammar (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.CheckedGrammar (packet (dimension old) old l r side w) := by
  refine ⟨?_,?_⟩
  · simp only [FormulaSignSlotRadialProviderAtomic.Canonical,packet,FormulaSignSlotRadialProviderAtomic.provider_packet,
      FormulaSignSlotRadialProviderAtomic.payload_packet,FormulaSignSlotRadialProviderAtomic.word_packet]
  · rw [dimension_packet,width_packet,sourceCap_packet,initial_packet,payload_packet]
    exact checked old hv hd l r side hE

theorem raw_count (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    WordListRecords.count (IntegralMixedRoadmapChain.raw (payload (dimension old) old l r side))=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload old)) := by
  rw [(checked old hv hd l r side hE).2.2.2.2.2.2.1,
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv)).2.2.2.2.2.2.1]

theorem prefix_record (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (l r : List Bool) (side : Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapChain.rawStart (dimension old) (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload (dimension old) old l r side)) i=
      WordList.get (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload old)) i :=
  IntegralMixedRoadmapChain.append_raw_before
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv))
    l r side (IntegralMixedRoadmapChain.seedCode _) i
    (by simpa only [FormulaSignSlotRadialProviderAtomic.depth] using hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
