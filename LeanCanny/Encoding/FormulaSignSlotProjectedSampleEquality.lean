/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualitySemantics
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSize
public import LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
public import LeanCanny.Encoding.IntegralMixedRoadmapWordLabel
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native comparison of the original coordinates of two OLD sampled labels -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def candidate (side : Bool) (H : List Bool) :=
  CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery side H)
noncomputable def context (side : Bool) (H : List Bool) :=
  FormulaSignSlotRadialOldProviderRealization.context (FormulaSignSlotRadialJointLayout.source side H) (candidate side H) []
theorem candidate_FP (side : Bool) : candidate side ∈ FP :=
  mem_FP_comp (FormulaSignSlotRadialJointLayout.labelQuery_FP side) CanonicalAuxiliaryCandidateLabels.candidate_FP
theorem context_FP (side : Bool) : context side ∈ FP :=
  mem_FP_pair (mem_FP_pair (FormulaSignSlotRadialJointLayout.source_FP side) (candidate_FP side)) (constFn_mem_FP (pair [false] []))
noncomputable def dimension := FormulaSignSlotRadialJointLayout.centerCount
theorem dimension_unary : UnaryFn dimension := FormulaSignSlotRadialJointLayout.centerCount_unary
noncomputable def vertexBudget (side : Bool) := FormulaSignSlotRadialProviderAtomic.providerVertexBudget ∘ context side
theorem vertexBudget_unary (side : Bool) : UnaryFn (vertexBudget side) :=
  FormulaSignSlotRadialProviderAtomic.providerVertexBudget_unary.comp (context_FP side)
noncomputable def rawBudget (H : List Bool) := 2*vertexBudget false H+vertexBudget true H+2
noncomputable def width (H : List Bool) := 2*rawBudget H+2
theorem rawBudget_unary : UnaryFn rawBudget :=
  (((UnaryFn.const 2).mul (vertexBudget_unary false)).add (vertexBudget_unary true)).add (UnaryFn.const 2)
theorem width_unary : UnaryFn width := ((UnaryFn.const 2).mul rawBudget_unary).add (UnaryFn.const 2)

def header (z : List Bool) := pairFst z
def left (z : List Bool) := pairFst (pairSnd z)
def right (z : List Bool) := pairSnd (pairSnd z)
def packet (H a b : List Bool) := pair H (pair a b)
theorem header_FP : header ∈ FP := pairFst_mem_FP
theorem left_FP : left ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem right_FP : right ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def fieldPacket (a b : List Bool) (i : ℕ) := FormulaSignSlotRadialProviderFieldEquality.packet
  (FormulaSignSlotRadialProviderAtomic.context a) (FormulaSignSlotRadialProviderAtomic.word a)
  (FormulaSignSlotRadialProviderAtomic.context b) (FormulaSignSlotRadialProviderAtomic.word b) i i
noncomputable def Holds (H a b : List Bool) : Prop := ∀ i<dimension H,
  fieldPacket a b i ∈ FormulaSignSlotRadialProviderFieldEquality.language
noncomputable def Witness (H a b : List Bool) : Prop :=
  FormulaSignSlotRadialProviderAtomic.Valid a ∧ FormulaSignSlotRadialProviderAtomic.Valid b ∧
  FormulaSignSlotRadialProviderAtomic.provider a=context false H ∧
  FormulaSignSlotRadialProviderAtomic.provider b=context true H ∧ Holds H a b

def fieldQuery (r : List Bool) := fieldPacket (left (pairFst r)) (right (pairFst r)) (pairSnd r).length
theorem fieldQuery_FP : fieldQuery ∈ FP := by
  have HC (f : List Bool → List Bool) (hf : f ∈ FP) :
      (fun r => FormulaSignSlotRadialProviderAtomic.context (f (pairFst r))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairFst_mem_FP hf) FormulaSignSlotRadialProviderAtomic.context_FP
  have HW (f : List Bool → List Bool) (hf : f ∈ FP) :
      (fun r => FormulaSignSlotRadialProviderAtomic.word (f (pairFst r))) ∈ FP :=
    mem_FP_comp (f := fun r => f (pairFst r)) (g := FormulaSignSlotRadialProviderAtomic.word)
      (mem_FP_comp pairFst_mem_FP hf) FormulaSignSlotRadialProviderAtomic.word_FP
  unfold fieldQuery fieldPacket FormulaSignSlotRadialProviderFieldEquality.packet
  exact mem_FP_pair (mem_FP_pair (HC left left_FP) (HW left left_FP))
    (mem_FP_pair (mem_FP_pair (HC right right_FP) (HW right right_FP))
      (mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP))

theorem holds_evaluator : SpaceFunction (fun z => [decide (Holds (header z) (left z) (right z))]) := by
  have E := (FormulaSignSlotRadialProviderFieldEquality.decider.precompose fieldQuery fieldQuery_FP).flagEvaluator
  exact (E.forall_unary (dimension_unary.comp header_FP)).congr (funext fun z => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds, fieldQuery, pairFst_pair, pairSnd_pair, List.length_replicate,
      Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq])
noncomputable def rawLanguage : Language := {z | Witness (header z) (left z) (right z)}
theorem raw_decider : SpaceDecider rawLanguage := by
  have EA := FormulaSignSlotRadialProviderAtomic.evaluator.precompose left left_FP
  have EB := FormulaSignSlotRadialProviderAtomic.evaluator.precompose right right_FP
  have HA := Brackets.stringEq_fppred (mem_FP_comp left_FP FormulaSignSlotRadialProviderAtomic.provider_FP)
    (mem_FP_comp header_FP (context_FP false))
  have HB := Brackets.stringEq_fppred (mem_FP_comp right_FP FormulaSignSlotRadialProviderAtomic.provider_FP)
    (mem_FP_comp header_FP (context_FP true))
  apply (EA.andFlags (EB.andFlags ((SpaceFunction.ofFP _ HA.flag_mem_FP).andFlags
    ((SpaceFunction.ofFP _ HB.flag_mem_FP).andFlags holds_evaluator)))).decider
    (fun v => decide (v=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [rawLanguage, Witness, Set.mem_ofPred_eq, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]

def probe (q : List Bool) := pair (pairFst q) (IntegralMixedRoadmapWordLabel.decode (pairSnd q))
theorem probe_FP : probe ∈ FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP)
noncomputable def Bounded (H : List Bool) : Prop := ∃ bits : List Bool,
  bits.length=width H ∧ probe (pair H bits)∈rawLanguage
noncomputable def language : Language := {H | Bounded H}
theorem bounded_evaluator : SpaceFunction (fun H => [decide (Bounded H)]) := by
  exact ((raw_decider.precompose probe probe_FP).flagEvaluator.exists_words width_unary).congr (funext fun H => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Bounded, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq])
theorem decider : SpaceDecider language := by
  apply bounded_evaluator.decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro H
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]
theorem mem_PSPACE : language ∈ PSPACE := decider.mem_PSPACE

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.Valid context candidate Holds

theorem witness_bound (H a b : List Bool) (h : Witness H a b) :
    (pair a b).length ≤ rawBudget H := by
  have HA := FormulaSignSlotRadialProviderAtomic.vertex_length_provider a h.1
  have HB := FormulaSignSlotRadialProviderAtomic.vertex_length_provider b h.2.1
  rw [h.2.2.1] at HA
  rw [h.2.2.2.1] at HB
  rw [pair_length]
  unfold rawBudget vertexBudget
  simp only [Function.comp_apply]
  omega

theorem language_iff (H : List Bool) : H∈language ↔ ∃ a b : List Bool, Witness H a b := by
  constructor
  · rintro ⟨bits,_,h⟩
    let z := probe (pair H bits)
    have HH : header z=H := by simp only [header,z,probe,pairFst_pair]
    have HZ : Witness (header z) (left z) (right z) := h
    rw [HH] at HZ
    exact ⟨left z,right z,HZ⟩
  · rintro ⟨a,b,h⟩
    let bits := IntegralMixedRoadmapWordLabel.encode (rawBudget H) (pair a b)
    refine ⟨bits,IntegralMixedRoadmapWordLabel.encode_length _ _ (witness_bound H a b h),?_⟩
    have HE : probe (pair H bits)=packet H a b := by
      simp only [probe,bits,packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapWordLabel.decode_encode]
    rw [HE]
    simpa only [rawLanguage,Witness,header,left,right,packet,pairFst_pair,pairSnd_pair,Set.mem_ofPred_eq] using h

end LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality
