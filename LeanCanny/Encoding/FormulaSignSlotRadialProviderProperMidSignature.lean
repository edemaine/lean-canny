/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicGrammar
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList
public import LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison

/-! # Paired midpoint matching compares both endpoints separately

The temporary signature substitutes the LEFT producer for the midpoint
height and appends the RIGHT producer. All other fields are the actual old
frozen or MID companion producers. No mean/unit comparator is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
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

local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "I"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

noncomputable def ownSignature (q : List Bool):=signature (D q) (I q) q
theorem ownSignature_FP : ownSignature∈FP:=
  signature_FP (FormulaSignSlotRadialProviderAtomic.dimension_unary) (FormulaSignSlotRadialProviderAtomic.initial_unary)
noncomputable def table (z : List Bool):=IntegralMixedPhysicalPointSignatureComparison.pairs (D (left z)+1)
  (ownSignature (left z)) (ownSignature (right z))
noncomputable def query (z : List Bool):=FormulaSignSlotRadialProviderFieldEqualityList.packet
  (FormulaSignSlotRadialProviderAtomic.context (left z)) (FormulaSignSlotRadialProviderAtomic.word (left z))
  (FormulaSignSlotRadialProviderAtomic.context (right z)) (FormulaSignSlotRadialProviderAtomic.word (right z)) (table z)

attribute [local irreducible] ownSignature

theorem table_FP : table∈FP:=by
  unfold table
  exact IntegralMixedPhysicalPointSignatureComparison.pairs_FP
    (((FormulaSignSlotRadialProviderAtomic.dimension_unary).comp left_FP).add (UnaryFn.const 1))
    (mem_FP_comp (f:=left) (g:=ownSignature) left_FP (ownSignature_FP)) (mem_FP_comp (f:=right) (g:=ownSignature) right_FP (ownSignature_FP))
theorem query_FP : query∈FP:=by
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_comp (f:=left) (g:=FormulaSignSlotRadialProviderAtomic.context) left_FP FormulaSignSlotRadialProviderAtomic.context_FP) (mem_FP_comp (f:=left) (g:=FormulaSignSlotRadialProviderAtomic.word) left_FP FormulaSignSlotRadialProviderAtomic.word_FP))
    (mem_FP_pair (mem_FP_pair (mem_FP_comp (f:=right) (g:=FormulaSignSlotRadialProviderAtomic.context) right_FP FormulaSignSlotRadialProviderAtomic.context_FP)
      (mem_FP_comp (f:=right) (g:=FormulaSignSlotRadialProviderAtomic.word) right_FP FormulaSignSlotRadialProviderAtomic.word_FP)) (table_FP))

noncomputable def Compatible (z : List Bool):=D (left z)=D (right z)∧
  FormulaSignSlotRadialProviderAtomic.depth (left z)=FormulaSignSlotRadialProviderAtomic.depth (right z)∧0<FormulaSignSlotRadialProviderAtomic.depth (left z)
theorem compatible_FP : FPPred (Compatible):=by
  have DL : BinaryFn (fun z=>D (left z)):=(BinaryFn.ofUnary (FormulaSignSlotRadialProviderAtomic.dimension_unary)).comp left_FP
  have DR : BinaryFn (fun z=>D (right z)):=(BinaryFn.ofUnary (FormulaSignSlotRadialProviderAtomic.dimension_unary)).comp right_FP
  have KL : BinaryFn (fun z=>FormulaSignSlotRadialProviderAtomic.depth (left z)):=
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderAtomic.depth_unary).comp left_FP
  have KR : BinaryFn (fun z=>FormulaSignSlotRadialProviderAtomic.depth (right z)):=
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderAtomic.depth_unary).comp right_FP
  exact (DL.eq DR).and ((KL.eq KR).and ((BinaryFn.const 0).lt KL))

noncomputable def language : Language:={z |Compatible z∧query z∈
  FormulaSignSlotRadialProviderFieldEqualityList.language}
theorem decider : SpaceDecider (language):=by
  have HC:=SpaceFunction.ofFP _ (compatible_FP).flag_mem_FP
  have HM:=((FormulaSignSlotRadialProviderFieldEqualityList.decider).precompose _
    (query_FP)).flagEvaluator
  apply (HC.andFlags HM).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
