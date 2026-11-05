/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicLayout
/-! # Atomic histories retain the literal OLD or EXTERNAL provider

The provider context remains the first field of the record root. Its own
external word is metadata; the atomic vertex carries a separate full word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (provider payload word : List Bool) := pair provider (pair payload word)
def provider (q : List Bool) := pairFst q
def payload (q : List Bool) := pairFst (pairSnd q)
def word (q : List Bool) := pairSnd (pairSnd q)
def original (q : List Bool) := FormulaSignSlotRadialProviderIntegerPlan.original (provider q)
def root (q : List Bool) := FormulaSignSlotRadialProviderRecordPlan.root
  (provider q) (IntegralMixedRoadmapChain.raw (payload q)) []
def context (q : List Bool) := pair (root q) []
def fullQuery (q : List Bool) := pair (root q) (word q)
def sampleQuery (q : List Bool) := pair (context q) (word q)
def depth (q : List Bool) := IntegralMixedRoadmapChain.depth (payload q)
def frozen (q : List Bool) := IntegralMixedRoadmapChain.frozen (payload q) (depth q)
abbrev free := IntegralMixedRoadmapAtomic.free
abbrev endBirth := IntegralMixedRoadmapAtomic.endBirth
abbrev anchor := IntegralMixedRoadmapAtomic.anchor
abbrev first := IntegralMixedRoadmapAtomic.first
def companionQuery (n initial : ℕ) (q : List Bool) := pair (sampleQuery q)
  (IntegralMixedPhysicalPointCompanionScan.descriptor (anchor n initial q) (first n initial q) (free n q))
def signature (n initial : ℕ) (q : List Bool) :=
  IntegralMixedChronologicalPointSignatureCode.code n (first n initial q) (frozen q)

theorem provider_FP : provider ∈ FP := pairFst_mem_FP
theorem payload_FP : payload ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem word_FP : word ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem original_FP : original ∈ FP := mem_FP_comp provider_FP FormulaSignSlotRadialExternalContext.original_FP
theorem root_FP : root ∈ FP := mem_FP_pair provider_FP
  (mem_FP_pair (mem_FP_comp (f := payload) (g := IntegralMixedRoadmapChain.raw)
    payload_FP IntegralMixedRoadmapChain.raw_FP) (constFn_mem_FP []))
theorem context_FP : context ∈ FP := mem_FP_pair root_FP (constFn_mem_FP [])
theorem fullQuery_FP : fullQuery ∈ FP := mem_FP_pair root_FP word_FP
theorem sampleQuery_FP : sampleQuery ∈ FP := mem_FP_pair context_FP word_FP
theorem depth_unary : UnaryFn depth := IntegralMixedRoadmapChain.depth_unary.comp payload_FP
theorem frozen_FP : frozen ∈ FP := IntegralMixedRoadmapChain.frozen_FP payload_FP depth_unary

theorem provider_packet (c p w : List Bool) : provider (packet c p w)=c := pairFst_pair _ _
theorem payload_packet (c p w : List Bool) : payload (packet c p w)=p := by
  simp only [payload,packet,pairSnd_pair,pairFst_pair]
theorem word_packet (c p w : List Bool) : word (packet c p w)=w := by
  simp only [word,packet,pairSnd_pair]
theorem root_provider (q : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext (root q)=provider q :=
  FormulaSignSlotRadialProviderRecordPlan.providerContext_root _ _ _
theorem root_records (q : List Bool) : IntegralMixedCausalRecordPlanBits.records (root q)=
    IntegralMixedRoadmapChain.raw (payload q) :=
  FormulaSignSlotRadialProviderRecordPlan.records_root _ _ _

theorem companionQuery_FP {n initial : List Bool → ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    (fun q => companionQuery (n q) (initial q) q) ∈ FP :=
  mem_FP_pair sampleQuery_FP (mem_FP_pair (IntegralMixedRoadmapAtomic.anchor_unary hn hi).mem_FP
    (mem_FP_pair (IntegralMixedRoadmapAtomic.first_unary hn hi).mem_FP
      (IntegralMixedRoadmapAtomic.free_unary hn).mem_FP))
theorem signature_FP {n initial : List Bool → ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    (fun q => signature (n q) (initial q) q) ∈ FP :=
  IntegralMixedChronologicalPointSignatureCode.code_FP hn
    (BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.first_unary hn hi)) frozen_FP
theorem frozen_count (q : List Bool) : WordListRecords.count (frozen q)=depth q :=
  IntegralMixedRoadmapChain.frozen_count _ _
theorem signature_count (n initial : ℕ) (q : List Bool) : WordListRecords.count (signature n initial q)=n+1 :=
  IntegralMixedChronologicalPointSignatureCode.code_count _ _ _

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
