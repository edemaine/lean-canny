/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendLayout
/-! # A retained equal level preserves the literal provider and checked budget -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev endpoint := IntegralMixedRoadmapRetainedAppend.endpoint
def payload (d : ℕ) (old : List Bool) (e : ℕ) := IntegralMixedRoadmapChain.appendPayload d
  (FormulaSignSlotRadialProviderAtomic.payload old) (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode d)
def packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :=
  FormulaSignSlotRadialProviderAtomic.packet (FormulaSignSlotRadialProviderAtomic.provider old) (payload d old e) w
theorem provider_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.provider (packet d old e w)=FormulaSignSlotRadialProviderAtomic.provider old :=
  FormulaSignSlotRadialProviderAtomic.provider_packet _ _ _
theorem payload_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.payload (packet d old e w)=payload d old e :=
  FormulaSignSlotRadialProviderAtomic.payload_packet _ _ _
theorem word_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.word (packet d old e w)=w :=
  FormulaSignSlotRadialProviderAtomic.word_packet _ _ _
theorem depth_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.depth (packet d old e w)=FormulaSignSlotRadialProviderAtomic.depth old+1 := by
  simp only [FormulaSignSlotRadialProviderAtomic.depth,payload_packet,payload,IntegralMixedRoadmapChain.append_depth]

theorem dimension_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.dimension (packet d old e w)=FormulaSignSlotRadialProviderAtomic.dimension old := by
  rw [FormulaSignSlotRadialProviderAtomic.dimension_provider,FormulaSignSlotRadialProviderAtomic.dimension_provider,
    provider_packet]
theorem initial_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.initial (packet d old e w)=FormulaSignSlotRadialProviderAtomic.initial old := by
  rw [FormulaSignSlotRadialProviderAtomic.initial_provider,FormulaSignSlotRadialProviderAtomic.initial_provider,provider_packet]
theorem width_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.width (packet d old e w)=FormulaSignSlotRadialProviderAtomic.width old := by
  rw [FormulaSignSlotRadialProviderAtomic.width_provider,FormulaSignSlotRadialProviderAtomic.width_provider,provider_packet]
theorem degree_provider (q : List Bool) : FormulaSignSlotRadialProviderRecordPlan.parameters.degree
    (FormulaSignSlotRadialProviderAtomic.root q)=FormulaSignSlotRadialProviderIntegerPlan.parameters.degree
      (FormulaSignSlotRadialProviderAtomic.provider q) := by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.degree
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root q))=_
  rw [FormulaSignSlotRadialProviderAtomic.root_provider]
theorem sourceCap_packet (d : ℕ) (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.sourceCap (packet d old e w)=FormulaSignSlotRadialProviderAtomic.sourceCap old := by
  unfold FormulaSignSlotRadialProviderAtomic.sourceCap
  rw [dimension_packet,degree_provider,degree_provider,provider_packet]

open FormulaSignSlotRadialProviderAtomic (dimension initial width sourceCap depth frozen endBirth ownBirth)

theorem level_good (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    IntegralMixedRoadmapLevel.Good (dimension old) (width old) (sourceCap old)
      (endBirth (dimension old) (initial old) old)
      (IntegralMixedRoadmapLevel.packet (frozen old) (endpoint e) (endpoint e) false []) := by
  unfold IntegralMixedRoadmapLevel.Good
  simp only [IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
  refine ⟨?_,?_,?_,?_,?_,FormulaSignSlotRadialProviderAtomic.sourceCap_le old,?_⟩
  · exact IntegralMixedRoadmapLevel.frame_mono (FormulaSignSlotRadialProviderAtomic.own_frame_good old hv)
      (by unfold ownBirth; omega)
  · simpa only [IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,FormulaSignSlotRadialProviderAtomic.frozen_count]
      using Nat.succ_lt_succ hd
  · exact IntegralMixedRoadmapRetainedAppend.endpoint_good _ _ _ _ _ _ _ he
  · exact IntegralMixedRoadmapRetainedAppend.endpoint_good _ _ _ _ _ _ _ he
  · left
    simp only [IntegralMixedRoadmapLevel.sideWord,pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false]
  · have HN : decide (([] : List Bool)=[true])=false := rfl
    simp only [IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.sideWord,IntegralMixedRoadmapLevel.slice,
      pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false,HN]

theorem checked (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    IntegralMixedRoadmapChain.Checked (dimension old) (width old) (sourceCap old) (initial old) (width old)
      (payload (dimension old) old e) := by
  have HG := level_good old hv hd e he
  simp only [IntegralMixedRoadmapAtomic.endBirth,FormulaSignSlotRadialProviderAtomic.frozen,
    FormulaSignSlotRadialProviderAtomic.depth] at HG
  simpa only [payload] using IntegralMixedRoadmapChain.append_checked
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv))
    (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode (dimension old)) hd HG
    (IntegralMixedRoadmapChain.seed _ _ _ ⟨0,by omega⟩).property

theorem grammar (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.CheckedGrammar (packet (dimension old) old e w) := by
  refine ⟨?_,?_⟩
  · simp only [FormulaSignSlotRadialProviderAtomic.Canonical,packet,FormulaSignSlotRadialProviderAtomic.provider_packet,
      FormulaSignSlotRadialProviderAtomic.payload_packet,FormulaSignSlotRadialProviderAtomic.word_packet]
  · rw [dimension_packet,width_packet,sourceCap_packet,initial_packet,payload_packet]
    exact checked old hv hd e he

theorem raw_count (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    WordListRecords.count (IntegralMixedRoadmapChain.raw (payload (dimension old) old e))=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload old)) := by
  rw [(checked old hv hd e he).2.2.2.2.2.2.1,
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv)).2.2.2.2.2.2.1]
theorem prefix_record (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old) (e i : ℕ)
    (hi : i<IntegralMixedRoadmapChain.rawStart (dimension old) (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload (dimension old) old e)) i=
      WordList.get (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload old)) i := by
  exact IntegralMixedRoadmapChain.append_raw_before
    (FormulaSignSlotRadialProviderAtomic.checked old (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv))
    (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode _) i hi

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
