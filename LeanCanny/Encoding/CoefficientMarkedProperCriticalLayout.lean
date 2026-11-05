/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalQuery
/-! # The actual no-critical prepared ROOT is original syntax only -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedProperCriticalLayout
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def code (n : List Bool → ℕ) (q : List Bool) := IntegralMixedChronologicalFrameCode.code
  (n (IntegralMixedRoadmapAtomic.original q) + 3) (IntegralMixedRoadmapProper.labels q)
  (IntegralMixedRoadmapProper.levelIndex q) (IntegralMixedRoadmapProper.levelIndex q)

theorem code_FP {n : List Bool → ℕ} (hn : UnaryFn n) : code n ∈ FP :=
  IntegralMixedChronologicalFrameCode.code_FP ((hn.comp IntegralMixedRoadmapAtomic.original_FP).add (UnaryFn.const 3))
    (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary)
    (BinaryFn.ofUnary IntegralMixedRoadmapProper.levelIndex_unary) IntegralMixedRoadmapProper.labels_FP

def query (n : List Bool → ℕ) (z : List Bool) := IntegralMixedPhysicalCriticalQuery.packet
  (IntegralMixedRoadmapProperCritical.prefixRoot (pairFst z)) (code n (pairFst z)) (pairSnd z)
  (IntegralMixedRoadmapProper.producer false (pairFst z)) (IntegralMixedRoadmapProper.producer true (pairFst z))

attribute [local irreducible] code IntegralMixedRoadmapProperCritical.prefixRoot
  IntegralMixedRoadmapProper.producer IntegralMixedPhysicalCriticalQuery.packet

theorem query_FP {n : List Bool → ℕ} (hn : UnaryFn n) : query n ∈ FP :=
  IntegralMixedPhysicalCriticalQuery.packet_FP
    (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapProperCritical.prefixRoot_FP)
    (mem_FP_comp pairFst_mem_FP (code_FP hn)) pairSnd_mem_FP
    ((IntegralMixedRoadmapProper.producer_binary false).comp pairFst_mem_FP)
    ((IntegralMixedRoadmapProper.producer_binary true).comp pairFst_mem_FP)

def canonical (n : List Bool → ℕ) (q : List Bool) := query n (pair q [])
def root (n : List Bool → ℕ) (q : List Bool) := IntegralMixedPhysicalCriticalQuery.root (canonical n q)
def context (n : List Bool → ℕ) (q : List Bool) := pair (root n q) []

attribute [local irreducible] query

theorem canonical_FP {n : List Bool → ℕ} (hn : UnaryFn n) : canonical n ∈ FP := by
  unfold canonical
  exact mem_FP_comp (f := fun q => pair q []) (g := query n)
    (mem_FP_pair id_mem_FP (constFn_mem_FP [])) (query_FP hn)

attribute [local irreducible] canonical

theorem root_FP {n : List Bool → ℕ} (hn : UnaryFn n) : root n ∈ FP :=
  mem_FP_comp (f := canonical n) (g := IntegralMixedPhysicalCriticalQuery.root)
    (canonical_FP hn) pairFst_mem_FP
attribute [local irreducible] root

theorem context_FP {n : List Bool → ℕ} (hn : UnaryFn n) : context n ∈ FP := mem_FP_pair (root_FP hn) (constFn_mem_FP [])

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

theorem native_code (q : List Bool) : IntegralMixedRoadmapProperCritical.code hn ht ha hR0 q = code n q := by
  unfold IntegralMixedRoadmapProperCritical.code code
  rw [IntegralMixedRoadmapAtomic.dimension_eq]

theorem native_query (z : List Bool) : IntegralMixedRoadmapProperCritical.query hn ht ha hR0 z = query n z := by
  unfold IntegralMixedRoadmapProperCritical.query query
  rw [native_code hn ht ha hR0]

theorem native_root (q : List Bool) : IntegralMixedRoadmapProperCritical.root hn ht ha hR0 q = root n q := by
  unfold IntegralMixedRoadmapProperCritical.root IntegralMixedRoadmapProperCritical.canonical root canonical
  rw [native_query hn ht ha hR0]

theorem native_context (q : List Bool) : IntegralMixedRoadmapProperCritical.context hn ht ha hR0 q = context n q := by
  unfold IntegralMixedRoadmapProperCritical.context context
  rw [native_root hn ht ha hR0]

/-- The prepared ROOT forgets the original atomic word too; only candidate,
history metadata, normalized frame code and endpoint producer labels remain. -/
theorem root_packet_words (candidate payload w v : List Bool) :
    root n (IntegralMixedRoadmapAtomic.packet candidate payload w) =
      root n (IntegralMixedRoadmapAtomic.packet candidate payload v) := by
  unfold root canonical query code IntegralMixedRoadmapProperCritical.prefixRoot
    IntegralMixedRoadmapProper.badPacket IntegralMixedRoadmapBadProbePacket.prefixWord
    IntegralMixedRoadmapBadProbePacket.prefixCodes IntegralMixedRoadmapBadProbePacket.count
    IntegralMixedRoadmapBadProbePacket.raw IntegralMixedRoadmapBadProbePacket.packet
    IntegralMixedRoadmapProper.labels IntegralMixedRoadmapProper.producer IntegralMixedRoadmapProper.levelIndex
  simp only [IntegralMixedRoadmapAtomic.original, IntegralMixedRoadmapAtomic.candidate,
    IntegralMixedRoadmapAtomic.payload, IntegralMixedRoadmapAtomic.word, IntegralMixedRoadmapAtomic.depth,
    IntegralMixedRoadmapAtomic.packet, pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.CoefficientMarkedProperCriticalLayout
