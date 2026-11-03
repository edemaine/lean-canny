/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison

/-! # Paired midpoint matching compares both endpoints separately

The temporary signature substitutes the LEFT producer for the midpoint
height and appends the RIGHT producer. All other fields are the actual old
frozen or MID companion producers. No mean/unit comparator is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def extendedLabels (q : List Bool):=IntegralMixedChronologicalEndpointCode.appendLabels
  (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
def signature (n initial : ℕ) (q : List Bool):=
  IntegralMixedChronologicalPointSignatureCode.code n (IntegralMixedRoadmapProper.midFirst n initial q) (extendedLabels q)++
    pair (BinaryNatCode.encode (IntegralMixedRoadmapProper.producer true q)) []
theorem extendedLabels_FP : extendedLabels∈FP:=IntegralMixedChronologicalEndpointCode.appendLabels_FP
  IntegralMixedRoadmapProper.labels_FP (IntegralMixedRoadmapProper.producer_binary false)
theorem signature_FP {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    (fun q=>signature (n q) (initial q) q)∈FP:=appendFn_mem_FP
  (IntegralMixedChronologicalPointSignatureCode.code_FP hn
    (BinaryFn.ofUnary (IntegralMixedRoadmapProper.midFirst_unary hn hi)) extendedLabels_FP)
  (mem_FP_pair (IntegralMixedRoadmapProper.producer_binary true).bits_mem_FP (constFn_mem_FP []))

theorem signature_count (n initial : ℕ) (q : List Bool) : WordListRecords.count (signature n initial q)=n+2:=by
  unfold signature IntegralMixedChronologicalPointSignatureCode.code
  change WordListRecords.count (WordList.encode ((List.range (n+1)).map _ )++
    WordList.encode [BinaryNatCode.encode (IntegralMixedRoadmapProper.producer true q)])=n+2
  rw [←IntegralMixedRoadmapLevel.encode_append,WordListRecords.count_encode,List.length_append,
    List.length_map,List.length_range,List.length_singleton]

def left (z : List Bool):=pairFst z
def right (z : List Bool):=pairSnd z
theorem left_FP : left∈FP:=pairFst_mem_FP
theorem right_FP : right∈FP:=pairSnd_mem_FP

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

noncomputable def ownSignature (q : List Bool):=signature (D q) (I q) q
theorem ownSignature_FP : ownSignature hn ht ha hR0∈FP:=
  signature_FP (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0) (IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0)
noncomputable def table (z : List Bool):=IntegralMixedPhysicalPointSignatureComparison.pairs (D (left z)+1)
  (ownSignature hn ht ha hR0 (left z)) (ownSignature hn ht ha hR0 (right z))
noncomputable def query (z : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (IntegralMixedRoadmapAtomic.context (left z)) (IntegralMixedRoadmapAtomic.word (left z))
  (IntegralMixedRoadmapAtomic.context (right z)) (IntegralMixedRoadmapAtomic.word (right z)) (table hn ht ha hR0 z)

attribute [local irreducible] ownSignature

theorem table_FP : table hn ht ha hR0∈FP:=by
  unfold table
  exact IntegralMixedPhysicalPointSignatureComparison.pairs_FP
    (((IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0).comp left_FP).add (UnaryFn.const 1))
    (mem_FP_comp (f:=left) (g:=ownSignature hn ht ha hR0) left_FP (ownSignature_FP hn ht ha hR0)) (mem_FP_comp (f:=right) (g:=ownSignature hn ht ha hR0) right_FP (ownSignature_FP hn ht ha hR0))
theorem query_FP : query hn ht ha hR0∈FP:=by
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_comp (f:=left) (g:=IntegralMixedRoadmapAtomic.context) left_FP IntegralMixedRoadmapAtomic.context_FP) (mem_FP_comp (f:=left) (g:=IntegralMixedRoadmapAtomic.word) left_FP IntegralMixedRoadmapAtomic.word_FP))
    (mem_FP_pair (mem_FP_pair (mem_FP_comp (f:=right) (g:=IntegralMixedRoadmapAtomic.context) right_FP IntegralMixedRoadmapAtomic.context_FP)
      (mem_FP_comp (f:=right) (g:=IntegralMixedRoadmapAtomic.word) right_FP IntegralMixedRoadmapAtomic.word_FP)) (table_FP hn ht ha hR0))

noncomputable def Compatible (z : List Bool):=D (left z)=D (right z)∧
  IntegralMixedRoadmapAtomic.depth (left z)=IntegralMixedRoadmapAtomic.depth (right z)∧0<IntegralMixedRoadmapAtomic.depth (left z)
theorem compatible_FP : FPPred (Compatible hn ht ha hR0):=by
  have DL : BinaryFn (fun z=>D (left z)):=(BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)).comp left_FP
  have DR : BinaryFn (fun z=>D (right z)):=(BinaryFn.ofUnary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)).comp right_FP
  have KL : BinaryFn (fun z=>IntegralMixedRoadmapAtomic.depth (left z)):=
    (BinaryFn.ofUnary IntegralMixedRoadmapAtomic.depth_unary).comp left_FP
  have KR : BinaryFn (fun z=>IntegralMixedRoadmapAtomic.depth (right z)):=
    (BinaryFn.ofUnary IntegralMixedRoadmapAtomic.depth_unary).comp right_FP
  exact (DL.eq DR).and ((KL.eq KR).and ((BinaryFn.const 0).lt KL))

noncomputable def language : Language:={z |Compatible hn ht ha hR0 z∧query hn ht ha hR0 z∈
  IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)}
theorem decider : SpaceDecider (language hn ht ha hR0):=by
  have HC:=SpaceFunction.ofFP _ (compatible_FP hn ht ha hR0).flag_mem_FP
  have HM:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose _
    (query_FP hn ht ha hR0)).flagEvaluator
  apply (HC.andFlags HM).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
