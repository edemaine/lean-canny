/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval

/-! # The latest coarse frame supplies a literal reserved h-critical query

Only the reserved last raw record is replaced. The prepared parent word is
an independent argument at the new root; the original atomic word stays
inside the base packet for old-field comparisons.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def prefixRoot (q : List Bool):=pair (FormulaSignSlotRadialProviderAtomic.provider q)
  (pair (IntegralMixedRoadmapBadProbePacket.prefixWord (IntegralMixedRoadmapProper.badPacket q)) [])
attribute [local irreducible] IntegralMixedRoadmapProper.badPacket

theorem prefixRoot_FP : prefixRoot∈FP:=mem_FP_pair FormulaSignSlotRadialProviderAtomic.provider_FP
  (mem_FP_pair (mem_FP_comp (f:=IntegralMixedRoadmapProper.badPacket) (g:=IntegralMixedRoadmapBadProbePacket.prefixWord)
    IntegralMixedRoadmapProper.badPacket_FP IntegralMixedRoadmapBadProbePacket.prefixWord_FP)
    (constFn_mem_FP []))

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

noncomputable def code (q : List Bool):=IntegralMixedChronologicalFrameCode.code
  (FormulaSignSlotRadialProviderAtomic.dimension q) (IntegralMixedRoadmapProper.labels q)
  (IntegralMixedRoadmapProper.levelIndex q) (IntegralMixedRoadmapProper.levelIndex q)
theorem code_FP : code∈FP:=IntegralMixedChronologicalFrameCode.code_FP
  (FormulaSignSlotRadialProviderAtomic.dimension_unary)
  (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary) (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary)
  IntegralMixedRoadmapProper.labels_FP

attribute [local irreducible] prefixRoot code IntegralMixedRoadmapProper.producer
  IntegralMixedPhysicalCriticalQuery.packet IntegralMixedPhysicalCriticalQuery.prepare

noncomputable def query (z : List Bool):=IntegralMixedPhysicalCriticalQuery.packet
  (prefixRoot (pairFst z)) (code (pairFst z)) (pairSnd z)
  (IntegralMixedRoadmapProper.producer false (pairFst z)) (IntegralMixedRoadmapProper.producer true (pairFst z))
theorem query_FP : query∈FP:=by
  unfold query
  exact IntegralMixedPhysicalCriticalQuery.packet_FP
    (ctx:=fun z=>prefixRoot (pairFst z)) (code:=fun z=>code (pairFst z)) (w:=pairSnd)
    (a:=fun z=>IntegralMixedRoadmapProper.producer false (pairFst z))
    (b:=fun z=>IntegralMixedRoadmapProper.producer true (pairFst z))
    (mem_FP_comp (f:=pairFst) (g:=prefixRoot) pairFst_mem_FP prefixRoot_FP)
    (mem_FP_comp (f:=pairFst) (g:=code) pairFst_mem_FP (code_FP)) pairSnd_mem_FP
    ((IntegralMixedRoadmapProper.producer_binary false).comp pairFst_mem_FP)
    ((IntegralMixedRoadmapProper.producer_binary true).comp pairFst_mem_FP)

attribute [local irreducible] query

noncomputable def canonical (q : List Bool):=query (pair q [])
noncomputable def root (q : List Bool):=IntegralMixedPhysicalCriticalQuery.root (canonical q)
noncomputable def context (q : List Bool):=pair (root q) []
theorem canonical_FP : canonical∈FP:=mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP [])) (query_FP)
theorem root_FP : root∈FP:=mem_FP_comp
  (f:=canonical) (g:=IntegralMixedPhysicalCriticalQuery.root) (canonical_FP) pairFst_mem_FP
theorem context_FP : context∈FP:=mem_FP_pair (root_FP) (constFn_mem_FP [])

theorem root_word (q w : List Bool) : IntegralMixedPhysicalCriticalQuery.root
    (query (pair q w))=root q :=by
  simp only [root,canonical,query,IntegralMixedPhysicalCriticalQuery.packet,
    IntegralMixedPhysicalCriticalQuery.root,pairFst_pair,pairSnd_pair]

theorem critical_query (q w : List Bool) : IntegralMixedPhysicalCriticalQuery.critical
    (query (pair q w)):=by
  simpa only [query,pairFst_pair,pairSnd_pair] using IntegralMixedPhysicalCriticalQuery.critical_packet (prefixRoot q) (code q) w
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
