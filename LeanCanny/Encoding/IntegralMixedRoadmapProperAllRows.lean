/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness

/-! # Every free coordinate has an actual ordinary/mean certificate

Packet: atomic vertex, fixed-width section word, list of pairs of OWN
ordinary/mean full words. Coordinate indices are generated from the latest
coarse depth, and rank digits are taken at relative-coordinate offsets.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAllRows
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (atomic sectionBits rows : List Bool):=pair atomic (pair sectionBits rows)
def atomic (q : List Bool):=pairFst q
def sectionWord (q : List Bool):=pairFst (pairSnd q)
def rows (q : List Bool):=pairSnd (pairSnd q)
def entry (z : List Bool):=WordList.get (rows (pairFst z)) (pairSnd z).length
def coordinate (z : List Bool):=IntegralMixedRoadmapProper.levelIndex (atomic (pairFst z))+1+(pairSnd z).length

theorem atomic_FP : atomic∈FP:=pairFst_mem_FP
theorem sectionWord_FP : sectionWord∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rows_FP : rows∈FP:=mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem entry_FP : entry∈FP:=by
  exact IntegralMixedRoadmapChain.get_FP (mem_FP_comp (f:=pairFst) (g:=rows) pairFst_mem_FP rows_FP) (BinaryFn.ofUnary UnaryFn.index)
theorem coordinate_unary : UnaryFn coordinate:=
  (((IntegralMixedRoadmapProper.levelIndex_unary.comp atomic_FP).comp pairFst_mem_FP).add (UnaryFn.const 1)).add UnaryFn.index

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "W"=>IntegralMixedRoadmapAtomic.width hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.width

noncomputable def count (q : List Bool):=IntegralMixedRoadmapProper.captureCount (D (atomic q)) (atomic q)
theorem count_unary : UnaryFn (count hn ht ha hR0):=
  (IntegralMixedRoadmapProper.captureCount_unary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)).comp atomic_FP
noncomputable def rankBits (z : List Bool):=((sectionWord (pairFst z)).drop
  ((pairSnd z).length*W (atomic (pairFst z)))).take (W (atomic (pairFst z)))
theorem rankBits_FP : rankBits hn ht ha hR0∈FP:=by
  have HW:=((IntegralMixedRoadmapAtomic.width_unary hn ht ha hR0).comp atomic_FP).comp pairFst_mem_FP
  exact take_mem_FP (drop_mem_FP (mem_FP_comp (f:=pairFst) (g:=sectionWord) pairFst_mem_FP sectionWord_FP) (UnaryFn.index.mul HW)) HW

noncomputable def query (z : List Bool):=IntegralMixedRoadmapProperRowWitness.packet
  (pair (atomic (pairFst z)) (BinaryNatCode.encode (coordinate z))) (pairFst (entry z)) (pairSnd (entry z))
  (rankBits hn ht ha hR0 z)
theorem query_FP : query hn ht ha hR0∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=atomic) pairFst_mem_FP atomic_FP) (BinaryFn.ofUnary coordinate_unary).bits_mem_FP)
  (mem_FP_pair (mem_FP_comp (f:=entry) (g:=pairFst) entry_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (f:=entry) (g:=pairSnd) entry_FP pairSnd_mem_FP) (rankBits_FP hn ht ha hR0)))

noncomputable def Grammar (q : List Bool):=0<IntegralMixedRoadmapAtomic.depth (atomic q)∧
  IntegralMixedRoadmapAtomic.depth (atomic q)≤D (atomic q)∧
  (sectionWord q).length=(D (atomic q)+1)*W (atomic q)∧WordListRecords.count (rows q)=count hn ht ha hR0 q

theorem grammar_FP : FPPred (Grammar hn ht ha hR0):=by
  have HK:=IntegralMixedRoadmapAtomic.depth_unary.comp atomic_FP
  have HD:=(IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0).comp atomic_FP
  have HW:=(IntegralMixedRoadmapAtomic.width_unary hn ht ha hR0).comp atomic_FP
  exact ((BinaryFn.const 0).lt (BinaryFn.ofUnary HK)).and
    (((BinaryFn.ofUnary HK).le (BinaryFn.ofUnary HD)).and
      (((BinaryFn.ofUnary (UnaryFn.length sectionWord_FP)).eq (BinaryFn.ofUnary ((HD.add (UnaryFn.const 1)).mul HW))).and
        ((BinaryFn.ofUnary (WordListRecords.count_unary.comp rows_FP)).eq (BinaryFn.ofUnary (count_unary hn ht ha hR0)))))

noncomputable def holds (right : Bool) (q : List Bool):=∀i<count hn ht ha hR0 q,
  query hn ht ha hR0 (pair q (List.replicate i true))∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right
noncomputable def language (right : Bool) : Language:={q |Grammar hn ht ha hR0 q∧holds hn ht ha hR0 right q}

theorem decider (right : Bool) : SpaceDecider (language hn ht ha hR0 right):=by
  have EG:=SpaceFunction.ofFP _ (grammar_FP hn ht ha hR0).flag_mem_FP
  have ER:=((IntegralMixedRoadmapProperRowWitness.decider hn ht ha hR0 right).precompose _ (query_FP hn ht ha hR0)).flagEvaluator
  have EA:=ER.forall_unary (count_unary hn ht ha hR0)
  apply (EG.andFlags EA).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,holds,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedRoadmapProperAllRows
