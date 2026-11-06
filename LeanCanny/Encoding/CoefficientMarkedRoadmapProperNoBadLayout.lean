/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapNoBadProbeTransport
public import LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicMetadata
public import LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicCutoff
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBase
/-! # The proper NoBad guard retains its literal atomic context and word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapProperNoBadLayout
open LeanCanny.Algebra LeanCanny.Computation
open CoefficientMarkedRoadmapAtomicMetadata (reword)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def request (q : List Bool) := pair (IntegralMixedRoadmapProper.badPacket (reword q [])) []

theorem request_FP : request ∈ FP := by
  have hr : (fun q => reword q []) ∈ FP := CoefficientMarkedRoadmapAtomicCutoff.canonical_FP
  have hp : (fun q => IntegralMixedRoadmapProper.badPacket (reword q [])) ∈ FP :=
    mem_FP_comp hr IntegralMixedRoadmapProper.badPacket_FP
  exact mem_FP_pair hp (constFn_mem_FP [])

theorem base_reword (q w : List Bool) : CoefficientMarkedRoadmapBadProbeTransport.base (request q) w =
    IntegralMixedRoadmapProper.badPacket (reword q w) := by
  simp only [CoefficientMarkedRoadmapBadProbeTransport.base, request, IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.labels,
    IntegralMixedRoadmapBadProbePacket.endpoints, IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapProper.producer, IntegralMixedRoadmapProper.levelIndex,
    IntegralMixedRoadmapAtomic.depth, reword, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload, IntegralMixedRoadmapAtomic.word,
    pairFst_pair, pairSnd_pair]

theorem leftContext_request (q : List Bool) : CoefficientMarkedRoadmapBadProbeTransport.leftContext (request q) =
    IntegralMixedRoadmapAtomic.context q := by
  simp only [CoefficientMarkedRoadmapBadProbeTransport.leftContext, CoefficientMarkedRoadmapBadProbeTransport.baseRoot,
    request, IntegralMixedRoadmapBadProbePacket.root, IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate,
    IntegralMixedRoadmapBadProbePacket.raw, reword, IntegralMixedRoadmapAtomic.packet,
    IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.payload,
    IntegralMixedRoadmapAtomic.context, IntegralMixedRoadmapAtomic.root, pairFst_pair, pairSnd_pair]

theorem leftRoot_request (q : List Bool) : CoefficientMarkedRoadmapBadProbeTransport.leftRoot (request q) =
    IntegralMixedRoadmapAtomic.root q :=
  (congrArg pairFst (leftContext_request q)).trans (pairFst_pair _ _)

theorem request_reword (q w : List Bool) : request (reword q w) = request q := by
  simp only [request, reword, IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.candidate,
    IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

theorem base_source (q : List Bool) :
    CoefficientMarkedRoadmapBadProbeTransport.base (request q) (IntegralMixedRoadmapAtomic.word q) =
      IntegralMixedRoadmapProper.badPacket q := by
  rw [base_reword]
  simp only [IntegralMixedRoadmapProper.badPacket, IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapProper.producer, IntegralMixedRoadmapProper.levelIndex, IntegralMixedRoadmapAtomic.depth,
    CoefficientMarkedRoadmapAtomicMetadata.candidate_reword, CoefficientMarkedRoadmapAtomicMetadata.payload_reword,
    CoefficientMarkedRoadmapAtomicMetadata.word_reword]

end LeanCanny.Encoding.CoefficientMarkedRoadmapProperNoBadLayout
