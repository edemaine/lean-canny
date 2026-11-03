/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval

/-! # The latest coarse frame supplies a literal reserved h-critical query

Only the reserved last raw record is replaced. The prepared parent word is
an independent argument at the new root; the original atomic word stays
inside the base packet for old-field comparisons.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def prefixRoot (q : List Bool):=pair (IntegralMixedRoadmapAtomic.candidate q)
  (pair (IntegralMixedRoadmapBadProbePacket.prefixWord (IntegralMixedRoadmapProper.badPacket q)) [])
attribute [local irreducible] IntegralMixedRoadmapProper.badPacket

theorem prefixRoot_FP : prefixRoot∈FP:=mem_FP_pair IntegralMixedRoadmapAtomic.candidate_FP
  (mem_FP_pair (mem_FP_comp (f:=IntegralMixedRoadmapProper.badPacket) (g:=IntegralMixedRoadmapBadProbePacket.prefixWord)
    IntegralMixedRoadmapProper.badPacket_FP IntegralMixedRoadmapBadProbePacket.prefixWord_FP)
    (constFn_mem_FP []))

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

noncomputable def code (q : List Bool):=IntegralMixedChronologicalFrameCode.code
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) (IntegralMixedRoadmapProper.labels q)
  (IntegralMixedRoadmapProper.levelIndex q) (IntegralMixedRoadmapProper.levelIndex q)
theorem code_FP : code hn ht ha hR0∈FP:=IntegralMixedChronologicalFrameCode.code_FP
  (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)
  (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary) (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary)
  IntegralMixedRoadmapProper.labels_FP

attribute [local irreducible] prefixRoot code IntegralMixedRoadmapProper.producer
  IntegralMixedPhysicalCriticalQuery.packet IntegralMixedPhysicalCriticalQuery.prepare

noncomputable def query (z : List Bool):=IntegralMixedPhysicalCriticalQuery.packet
  (prefixRoot (pairFst z)) (code hn ht ha hR0 (pairFst z)) (pairSnd z)
  (IntegralMixedRoadmapProper.producer false (pairFst z)) (IntegralMixedRoadmapProper.producer true (pairFst z))
theorem query_FP : query hn ht ha hR0∈FP:=by
  unfold query
  exact IntegralMixedPhysicalCriticalQuery.packet_FP
    (ctx:=fun z=>prefixRoot (pairFst z)) (code:=fun z=>code hn ht ha hR0 (pairFst z)) (w:=pairSnd)
    (a:=fun z=>IntegralMixedRoadmapProper.producer false (pairFst z))
    (b:=fun z=>IntegralMixedRoadmapProper.producer true (pairFst z))
    (mem_FP_comp (f:=pairFst) (g:=prefixRoot) pairFst_mem_FP prefixRoot_FP)
    (mem_FP_comp (f:=pairFst) (g:=code hn ht ha hR0) pairFst_mem_FP (code_FP hn ht ha hR0)) pairSnd_mem_FP
    ((IntegralMixedRoadmapProper.producer_binary false).comp pairFst_mem_FP)
    ((IntegralMixedRoadmapProper.producer_binary true).comp pairFst_mem_FP)

attribute [local irreducible] query

noncomputable def canonical (q : List Bool):=query hn ht ha hR0 (pair q [])
noncomputable def root (q : List Bool):=IntegralMixedPhysicalCriticalQuery.root (canonical hn ht ha hR0 q)
noncomputable def context (q : List Bool):=pair (root hn ht ha hR0 q) []
theorem canonical_FP : canonical hn ht ha hR0∈FP:=mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP [])) (query_FP hn ht ha hR0)
theorem root_FP : root hn ht ha hR0∈FP:=mem_FP_comp
  (f:=canonical hn ht ha hR0) (g:=IntegralMixedPhysicalCriticalQuery.root) (canonical_FP hn ht ha hR0) pairFst_mem_FP
theorem context_FP : context hn ht ha hR0∈FP:=mem_FP_pair (root_FP hn ht ha hR0) (constFn_mem_FP [])

theorem root_word (q w : List Bool) : IntegralMixedPhysicalCriticalQuery.root
    (query hn ht ha hR0 (pair q w))=root hn ht ha hR0 q :=by
  simp only [root,canonical,query,IntegralMixedPhysicalCriticalQuery.packet,
    IntegralMixedPhysicalCriticalQuery.root,pairFst_pair,pairSnd_pair]

theorem critical_query (q w : List Bool) : IntegralMixedPhysicalCriticalQuery.critical
    (query hn ht ha hR0 (pair q w)):=by
  simpa only [query,pairFst_pair,pairSnd_pair] using IntegralMixedPhysicalCriticalQuery.critical_packet (prefixRoot q) (code hn ht ha hR0 q) w
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
