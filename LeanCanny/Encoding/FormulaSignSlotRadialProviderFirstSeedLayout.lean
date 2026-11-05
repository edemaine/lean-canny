/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicValid
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadataCode
/-! # Literal depth-zero seed syntax for either integer provider -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def dim (c : List Bool) := FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient c
abbrev payload := IntegralMixedRoadmapSeedResampling.payload
noncomputable def packet (c w : List Bool) := FormulaSignSlotRadialProviderAtomic.packet c (payload (dim c)) w
noncomputable def root (c : List Bool) := FormulaSignSlotRadialProviderRecordPlan.root c
  (IntegralMixedRoadmapChain.raw (payload (dim c))) []
noncomputable def tail (c : List Bool) := IntegralMixedRoadmapChain.paddingCount (dim c) (payload (dim c))+1

theorem provider_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.provider (packet c w)=c :=
  FormulaSignSlotRadialProviderAtomic.provider_packet _ _ _
theorem payload_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.payload (packet c w)=payload (dim c) :=
  FormulaSignSlotRadialProviderAtomic.payload_packet _ _ _
theorem word_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.word (packet c w)=w :=
  FormulaSignSlotRadialProviderAtomic.word_packet _ _ _
theorem root_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.root (packet c w)=root c := by
  simp only [FormulaSignSlotRadialProviderAtomic.root,provider_packet,payload_packet,root]
theorem context_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.context (packet c w)=pair (root c) [] :=
  congrArg (fun r=>pair r []) (root_packet c w)
theorem dimension_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.dimension (packet c w)=dim c := by
  rw [FormulaSignSlotRadialProviderAtomic.dimension_provider,provider_packet]
  rfl
theorem initial_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.initial (packet c w)=
    FormulaSignSlotRadialProviderIntegerPlan.count c := by
  rw [FormulaSignSlotRadialProviderAtomic.initial_provider,provider_packet]
theorem width_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.width (packet c w)=
    FormulaSignSlotRadialProviderIntegerPlan.parameters.width c := by
  rw [FormulaSignSlotRadialProviderAtomic.width_provider,provider_packet]
theorem depth_packet (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.depth (packet c w)=0 := by
  simp only [FormulaSignSlotRadialProviderAtomic.depth,payload_packet,payload,IntegralMixedRoadmapSeedResampling.payload,
    IntegralMixedRoadmapChain.depth,IntegralMixedRoadmapChain.completePayload_metadata,
    show WordListRecords.count ([] : List Bool)=0 from WordListRecords.count_encode []]

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.width FormulaSignSlotRadialProviderAtomic.sourceCap
  FormulaSignSlotRadialProviderAtomic.initial dim

theorem checked (c w : List Bool) : FormulaSignSlotRadialProviderAtomic.CheckedGrammar (packet c w) := by
  constructor
  · simp only [FormulaSignSlotRadialProviderAtomic.Canonical,packet,FormulaSignSlotRadialProviderAtomic.provider_packet,
      FormulaSignSlotRadialProviderAtomic.payload_packet,FormulaSignSlotRadialProviderAtomic.word_packet]
  · rw [payload_packet,dimension_packet]
    exact IntegralMixedRoadmapChain.complete_seed_checked _ _ _ _ _ le_rfl
      (FormulaSignSlotRadialProviderAtomic.sourceCap_le _)

theorem root_provider (c : List Bool) : FormulaSignSlotRadialProviderRecordPlan.providerContext (root c)=c :=
  FormulaSignSlotRadialProviderRecordPlan.providerContext_root _ _ _
theorem count_root (c : List Bool) : FormulaSignSlotRadialProviderRecordPlan.count (root c)=
    FormulaSignSlotRadialProviderIntegerPlan.count c := by
  unfold FormulaSignSlotRadialProviderRecordPlan.count
  rw [root_provider]
theorem ambient_root (c : List Bool) : FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (root c)=dim c := by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root c))=dim c
  rw [root_provider]
  unfold dim
  rfl

theorem records_root (c : List Bool) : IntegralMixedCausalRecordPlanBits.records (root c)=
    IntegralMixedRoadmapChain.raw (payload (dim c)) :=
  FormulaSignSlotRadialProviderRecordPlan.records_root _ _ _
theorem raw_exact (c : List Bool) : IntegralMixedCausalRecordPlanBits.records (root c)=WordList.encode
    (IntegralMixedRoadmapChain.seedCodes (dim c)++List.replicate (tail c) (IntegralMixedRoadmapChain.seedCode (dim c))) :=
  (records_root c).trans (IntegralMixedRoadmapSeedResampling.raw_exact (dim c))
theorem raw_count (c : List Bool) : IntegralMixedCausalRecordPlanBits.count (root c)=
    IntegralMixedRoadmapRecordChain.probedRecordBound (dim c) := by
  rw [IntegralMixedCausalRecordPlanBits.count,records_root]
  exact IntegralMixedRoadmapSeedResampling.raw_count (dim c)
theorem raw_code (c : List Bool) (j : ℕ) (hj : j<IntegralMixedCausalRecordPlanBits.count (root c)) :
    IntegralMixedCausalRecordPlanBits.code (root c) j=IntegralMixedChronologicalFrameCode.code (dim c) [] 0
      (IntegralMixedRoadmapSeedMetadata.selected (dim c) j) := by
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [records_root]
  exact IntegralMixedRoadmapSeedMetadata.raw_lookup (dim c) j (by
    simpa only [IntegralMixedCausalRecordPlanBits.count,records_root] using hj)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
