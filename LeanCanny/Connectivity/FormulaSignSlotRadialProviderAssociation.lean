/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphCoding
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Actual OLD/EXTERNAL association has an internally bounded native checker

The witness is an accepted reachable OLD-provider vertex whose entire current
point agrees with the external vertex. Its geometric interpretation is separate.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def left (z : List Bool) :=pairFst z
def right (z : List Bool) :=pairSnd z
def provider (z : List Bool) :=FormulaSignSlotRadialProviderAtomic.provider (left z)
theorem left_FP : left∈FP:=pairFst_mem_FP
theorem right_FP : right∈FP:=pairSnd_mem_FP
theorem provider_FP : provider∈FP:=mem_FP_comp left_FP FormulaSignSlotRadialProviderAtomic.provider_FP

noncomputable def Header (z : List Bool) : Prop :=
  FormulaSignSlotRadialProviderAtomic.depth (left z)=0 ∧
  FormulaSignSlotRadialProviderAtomic.depth (right z)=0 ∧
  provider z=FormulaSignSlotRadialProviderPair.oldOf (FormulaSignSlotRadialProviderAtomic.provider (right z)) ∧
  FormulaSignSlotRadialExternalContext.external (FormulaSignSlotRadialProviderAtomic.provider (right z))

theorem header_FP : FPPred Header := by
  have HL : BinaryFn (fun z=>FormulaSignSlotRadialProviderAtomic.depth (left z)) :=
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderAtomic.depth_unary).comp left_FP
  have HR : BinaryFn (fun z=>FormulaSignSlotRadialProviderAtomic.depth (right z)) :=
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderAtomic.depth_unary).comp right_FP
  have HP : (fun z=>FormulaSignSlotRadialProviderAtomic.provider (right z))∈FP :=
    mem_FP_comp right_FP FormulaSignSlotRadialProviderAtomic.provider_FP
  exact ((HL.eq (BinaryFn.const 0)).and ((HR.eq (BinaryFn.const 0)).and
    ((Brackets.stringEq_fppred provider_FP (mem_FP_comp HP FormulaSignSlotRadialProviderPair.oldOf_FP)).and
      (FormulaSignSlotRadialExternalContext.external_FP.comp HP))))

noncomputable def Guards (z : List Bool) : Prop :=
  FormulaSignSlotRadialProviderAtomic.Valid (left z) ∧
  FormulaSignSlotRadialProviderAtomic.Valid (right z) ∧Header z

theorem guards_evaluator : SpaceFunction (fun z=>[decide (Guards z)]) := by
  have EL := FormulaSignSlotRadialProviderAtomic.evaluator.precompose left left_FP
  have ER := FormulaSignSlotRadialProviderAtomic.evaluator.precompose right right_FP
  have EH := SpaceFunction.ofFP _ header_FP.flag_mem_FP
  exact (EL.andFlags (ER.andFlags EH)).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

def witness (q : List Bool) :=IntegralMixedRoadmapWordLabel.decode (pairSnd q)
def reachQuery (q : List Bool) :=pair (provider (pairFst q)) (pair (left (pairFst q)) (witness q))
def crossQuery (q : List Bool) :=pair (witness q) (right (pairFst q))
theorem witness_FP : witness∈FP:=mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP
theorem reachQuery_FP : reachQuery∈FP:=mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=provider) pairFst_mem_FP provider_FP)
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP left_FP) witness_FP)
theorem crossQuery_FP : crossQuery∈FP:=mem_FP_pair witness_FP (mem_FP_comp pairFst_mem_FP right_FP)

noncomputable def witnessLanguage : Language := {q |reachQuery q∈FormulaSignSlotRadialProviderGraph.nativeReachLanguage ∧
  crossQuery q∈FormulaSignSlotRadialProviderCrossPoint.language}

theorem witness_decider : SpaceDecider witnessLanguage := by
  have ER := (FormulaSignSlotRadialProviderGraph.native_reach_decider.precompose reachQuery reachQuery_FP).flagEvaluator
  have EC := (FormulaSignSlotRadialProviderCrossPoint.decider.precompose crossQuery crossQuery_FP).flagEvaluator
  apply (ER.andFlags EC).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def width (z : List Bool) :=FormulaSignSlotRadialProviderGraph.width (provider z)
theorem width_unary : UnaryFn width:=FormulaSignSlotRadialProviderGraph.width_unary.comp provider_FP
noncomputable def BoundedWitness (z : List Bool) : Prop :=∃bits : List Bool,
  bits.length=width z ∧pair z bits∈witnessLanguage

theorem boundedWitness_evaluator : SpaceFunction (fun z=>[decide (BoundedWitness z)]) := by
  exact (witness_decider.flagEvaluator.exists_words width_unary).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [BoundedWitness,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def NativeWitness (a ext : List Bool) : Prop :=∃r,
  FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider a) a r ∧
    pair r ext∈FormulaSignSlotRadialProviderCrossPoint.language

noncomputable def Associated (a ext : List Bool) : Prop :=Guards (pair a ext)∧NativeWitness a ext

/-- The literal raw witness has a provider-derived polynomial byte bound. -/
theorem witness_byte_bound (a r : List Bool)
    (h : FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider a) a r) :
    r.length≤FormulaSignSlotRadialProviderAtomic.providerVertexBudget (FormulaSignSlotRadialProviderAtomic.provider a) := by
  have H := FormulaSignSlotRadialProviderAtomic.vertex_length_provider r h.2.1
  rw [h.2.2.2.1] at H
  exact H

theorem boundedWitness_iff (z : List Bool) : BoundedWitness z↔NativeWitness (left z) (right z) := by
  constructor
  · rintro ⟨bits,_,HR,HC⟩
    refine ⟨witness (pair z bits),?_,?_⟩
    · simpa only [FormulaSignSlotRadialProviderGraph.nativeReachLanguage,Set.mem_ofPred_eq,
        reachQuery,provider,FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,
        pairFst_pair,pairSnd_pair] using HR
    · simpa only [crossQuery,pairFst_pair] using HC
  · rintro ⟨r,HR,HC⟩
    have HB := witness_byte_bound (left z) r HR
    let bits := IntegralMixedRoadmapWordLabel.encode
      (FormulaSignSlotRadialProviderAtomic.providerVertexBudget (provider z)) r
    refine ⟨bits,IntegralMixedRoadmapWordLabel.encode_length _ r HB,?_,?_⟩
    · simpa only [FormulaSignSlotRadialProviderGraph.nativeReachLanguage,Set.mem_ofPred_eq,reachQuery,
        FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,witness,bits,
        pairFst_pair,pairSnd_pair,IntegralMixedRoadmapWordLabel.decode_encode,provider] using HR
    · simpa only [crossQuery,witness,bits,pairFst_pair,pairSnd_pair,
        IntegralMixedRoadmapWordLabel.decode_encode] using HC

noncomputable def language : Language :={z |Guards z∧BoundedWitness z}

theorem decider : SpaceDecider language := by
  apply (guards_evaluator.andFlags boundedWitness_evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language∈PSPACE:=decider.mem_PSPACE

theorem language_iff (a ext : List Bool) : pair a ext∈language↔Associated a ext := by
  change (Guards (pair a ext)∧BoundedWitness (pair a ext))↔_
  rw [boundedWitness_iff]
  simp only [Associated,left,right,pairFst_pair,pairSnd_pair]

theorem old_role_of_guards (z : List Bool) (h : Guards z) :
    ¬FormulaSignSlotRadialExternalContext.external (provider z) := by
  rw [h.2.2.2.2.1]
  exact FormulaSignSlotRadialProviderPair.old_role _

theorem language_packet_iff (a ext : List Bool)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (he : FormulaSignSlotRadialProviderAtomic.Valid ext)
    (hda : FormulaSignSlotRadialProviderAtomic.depth a=0) (hde : FormulaSignSlotRadialProviderAtomic.depth ext=0)
    (hp : FormulaSignSlotRadialProviderAtomic.provider a=
      FormulaSignSlotRadialProviderPair.oldOf (FormulaSignSlotRadialProviderAtomic.provider ext))
    (hx : FormulaSignSlotRadialExternalContext.external (FormulaSignSlotRadialProviderAtomic.provider ext)) :
    pair a ext∈language↔∃r,
      FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider a) a r ∧
        pair r ext∈FormulaSignSlotRadialProviderCrossPoint.language := by
  rw [language_iff]
  simp only [Associated,NativeWitness,Guards,Header,left,right,provider,pairFst_pair,pairSnd_pair,ha,he,hda,hde,hp,hx,
    true_and]

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
