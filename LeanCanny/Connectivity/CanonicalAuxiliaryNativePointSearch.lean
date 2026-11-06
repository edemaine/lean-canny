/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryNativeGraph
public import LeanCanny.Connectivity.CanonicalEndpointSampleBits
public import LeanCanny.Connectivity.EndpointValidation
public import LeanCanny.Connectivity.CanonicalWholeDecision
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Exact singleton endpoint search over the original frontier samples -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryNativePointSearch
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (p:List Bool):=pairFst (pairFst p)
def left (p:List Bool):=pairSnd (pairFst p)
def right (p:List Bool):=pairSnd p
noncomputable def width (c:List Bool):=CanonicalAuxiliaryCandidateCover.tagWidth (CanonicalEndpointSampleBits.frame c)
theorem width_unary:UnaryFn width:=CanonicalAuxiliaryCandidateCover.tagWidth_unary.comp CanonicalEndpointSampleBits.frame_FP
def endpointQuery (side:Bool) (p:List Bool):=pair (context p) (if side then right p else left p)
theorem endpointQuery_FP (side:Bool):endpointQuery side∈FP:=by
  cases side <;>polytime [endpointQuery,context,left,right]
noncomputable def graphQuery (p:List Bool):=pair (CanonicalEndpointSampleBits.frame (context p)) (pair (left p) (right p))
theorem graphQuery_FP:graphQuery∈FP:=by
  have HF:(fun p=>CanonicalEndpointSampleBits.frame (context p))∈FP:=mem_FP_comp
    (f:=context) (g:=CanonicalEndpointSampleBits.frame) (show context∈FP by polytime [context]) CanonicalEndpointSampleBits.frame_FP
  exact mem_FP_pair HF (by polytime [left,right])
noncomputable def Endpoint (side:Bool) (p:List Bool):Prop:=CanonicalEndpointSampleBits.value side (endpointQuery side p)=true
noncomputable def At (p:List Bool):Prop:=Endpoint false p ∧Endpoint true p ∧CanonicalAuxiliaryNativeGraph.Reachable (graphQuery p)

variable (D:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.language)
private theorem endpoint_evaluator (side:Bool):SpaceFunction (fun p=>[decide (Endpoint side p)]):=by
  have E:=(CanonicalEndpointSampleBits.evaluator side).precompose (endpointQuery side) (endpointQuery_FP side)
  exact E.congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Endpoint,decide_eq_true_eq])
include D in
theorem at_evaluator:SpaceFunction (fun p=>[decide (At p)]):=
  IntegralPolynomialWindowTarskiDecision.flag_and _ _ (endpoint_evaluator false)
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ (endpoint_evaluator true)
      ((CanonicalAuxiliaryNativeGraph.evaluator D).precompose graphQuery graphQuery_FP))

noncomputable def Holds (c:List Bool):Prop:=∃a:List Bool,a.length=width c ∧∃b:List Bool,b.length=width c∧At (pair (pair c a) b)
include D in
theorem holds_evaluator:SpaceFunction (fun c=>[decide (Holds c)]):=by
  have EB:=(at_evaluator D).exists_words (width_unary.comp pairFst_mem_FP)
  have EA:=EB.exists_words width_unary
  exact EA.congr (funext fun c=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def WellFormed (c:List Bool):Prop:=(CanonicalEndpointNative.description c).WellFormed
noncomputable def PointInput (c:List Bool):Prop:=Input.IsPoint c
noncomputable def language:Language:={c|PointInput c∧WellFormed c ∧c∈EndpointValidation.validEndpointLanguage∧Holds c}
include D in
theorem decider:SpaceDecider language:=by
  have EW:FPPred WellFormed:=FPPred.of_computable CanonicalEndpointNative.wellFormed_computable (fun c=>by
    simp only [WellFormed,decide_eq_true_eq])
  have EE:=(SpaceDecider.ofPSPACE EndpointValidation.validEndpoints_mem_PSPACE).flagEvaluator
  have EP:FPPred PointInput:=Input.isPoint_fppred
  have E:=IntegralPolynomialWindowTarskiDecision.flag_and _ _
    (SpaceFunction.ofFP _ EP.flag_mem_FP)
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ (SpaceFunction.ofFP _ EW.flag_mem_FP)
      (IntegralPolynomialWindowTarskiDecision.flag_and _ _ EE (holds_evaluator D)))
  apply E.decider (fun z=>decide (z=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
include D in
theorem mem_PSPACE:language∈PSPACE:=(decider D).mem_PSPACE

private theorem denotes_of_holds {n:ℕ} {p:Formula} (H:∃x:Fin n→ℝ,Denotes n p x) (v:Fin n→ℝ)
    (hv:p.Holds (Formula.extend v)):Denotes n p v:=by
  obtain ⟨x,hx⟩:=H
  have HE:v=x:=(hx.2 v).mp hv
  exact HE.symm ▸ hx

def packet (c a b:List Bool):=pair (pair c a) b
private theorem graph_packet (c a b:List Bool):graphQuery (packet c a b)=pair (CanonicalEndpointSampleBits.frame c) (pair a b):=by
  simp only [graphQuery,context,left,right,packet,pairFst_pair,pairSnd_pair]
private theorem endpoint_packet (side:Bool) (c a b:List Bool):endpointQuery side (packet c a b)=pair c (if side then b else a):=by
  simp only [endpointQuery,context,left,right,packet,pairFst_pair,pairSnd_pair]

attribute [local irreducible] CanonicalEndpointSampleBits.value CanonicalAuxiliaryCandidateCover.rawSample
  CanonicalAuxiliaryProjectedSamples.Good CanonicalAuxiliaryNativeGraph.Reachable

theorem holds_point_iff (q:PointQuery) (hd:q.space.WellFormed)
    (HE:(∃x:Fin q.space.dimension→ℝ,Denotes q.space.dimension q.source x) ∧
      (∃y:Fin q.space.dimension→ℝ,Denotes q.space.dimension q.target y)):
    Holds (Input.point q).encode ↔(Input.point q).encode∈pointLanguage:=by
  have hs:q.source.arity≤q.space.dimension:=HE.1.choose_spec.1
  have ht:q.target.arity≤q.space.dimension:=HE.2.choose_spec.1
  let d:=(CanonicalAuxiliarySampleEndpoints.expose q).space
  have hd':d.WellFormed:=CanonicalAuxiliarySampleEndpoints.expose_wellFormed q hd hs ht
  have HF:CanonicalEndpointSampleBits.frame (Input.point q).encode=CanonicalSignRefinement.original d:=
    CanonicalEndpointSampleBits.frame_point q
  rw [CanonicalAuxiliarySampleEndpoints.original_point_iff_samples q hd hs ht]
  constructor
  · rintro ⟨a,ha,b,hb,HS,HT,HR⟩
    change CanonicalAuxiliaryNativeGraph.Reachable (graphQuery (packet (Input.point q).encode a b)) at HR
    rw [graph_packet] at HR
    have HW:=(CanonicalAuxiliaryNativeGraph.reachable_packet _ a b ha hb).mp HR
    have VA:CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalEndpointSampleBits.frame (Input.point q).encode) a):=
      of_decide_eq_true HW.1
    have VB:CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalEndpointSampleBits.frame (Input.point q).encode) b):=
      of_decide_eq_true HW.2.1
    rw [HF] at VA VB HW
    let i:=CanonicalAuxiliaryCandidateLabels.decode d a VA
    let j:=CanonicalAuxiliaryCandidateLabels.decode d b VB
    have HA:CanonicalAuxiliaryCandidateCover.encode d i=a:=CanonicalAuxiliaryCandidateLabels.encode_decode d a VA
    have HB:CanonicalAuxiliaryCandidateCover.encode d j=b:=CanonicalAuxiliaryCandidateLabels.encode_decode d b VB
    have hi:CanonicalAuxiliaryProjectedSamples.Good d i:=by
      unfold CanonicalAuxiliaryProjectedSamples.Good
      exact (CanonicalAuxiliaryCandidateLabels.valid_encode_iff d i).mp (HA.symm ▸ VA)
    have hj:CanonicalAuxiliaryProjectedSamples.Good d j:=by
      unfold CanonicalAuxiliaryProjectedSamples.Good
      exact (CanonicalAuxiliaryCandidateLabels.valid_encode_iff d j).mp (HB.symm ▸ VB)
    have HSource:CanonicalEndpointSampleBits.value false (pair (Input.point q).encode a)=true:=by
      simpa only [Endpoint,endpointQuery,context,left,right,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false] using HS
    have HTarget:CanonicalEndpointSampleBits.value true (pair (Input.point q).encode b)=true:=by
      simpa only [Endpoint,endpointQuery,context,left,right,pairFst_pair,pairSnd_pair,ite_true] using HT
    rw [←HA,CanonicalEndpointSampleBits.value_source_point q i hi hs] at HSource
    rw [←HB,CanonicalEndpointSampleBits.value_target_point q j hj ht] at HTarget
    refine ⟨i,j,hi,hj,denotes_of_holds HE.1 _ (of_decide_eq_true HSource),
      denotes_of_holds HE.2 _ (of_decide_eq_true HTarget),?_⟩
    apply (CanonicalAuxiliaryNativeGraph.reachable_encoded_iff d hd' i j hi hj).mp
    simpa only [HA,HB] using HW
  · rintro ⟨i,j,hi,hj,HX,HY,HW⟩
    let a:=CanonicalAuxiliaryCandidateCover.encode d i
    let b:=CanonicalAuxiliaryCandidateCover.encode d j
    have HA:a.length=width (Input.point q).encode:=by
      simpa only [width,HF] using CanonicalAuxiliaryCandidateCover.encode_length d i
    have HB:b.length=width (Input.point q).encode:=by
      simpa only [width,HF] using CanonicalAuxiliaryCandidateCover.encode_length d j
    refine ⟨a,HA,b,HB,?_,?_,?_⟩
    · change CanonicalEndpointSampleBits.value false (endpointQuery false (packet (Input.point q).encode a b))=true
      rw [endpoint_packet]
      simp only [Bool.false_eq_true,ite_false]
      rw [CanonicalEndpointSampleBits.value_source_point q i hi hs]
      exact decide_eq_true ((HX.2 _).mpr rfl)
    · change CanonicalEndpointSampleBits.value true (endpointQuery true (packet (Input.point q).encode a b))=true
      rw [endpoint_packet]
      simp only [ite_true]
      rw [CanonicalEndpointSampleBits.value_target_point q j hj ht]
      exact decide_eq_true ((HY.2 _).mpr rfl)
    · change CanonicalAuxiliaryNativeGraph.Reachable (graphQuery (packet (Input.point q).encode a b))
      rw [graph_packet]
      apply (CanonicalAuxiliaryNativeGraph.reachable_packet _ a b HA HB).mpr
      rw [HF]
      exact (CanonicalAuxiliaryNativeGraph.reachable_encoded_iff d hd' i j hi hj).mpr HW

theorem language_point_iff (q:PointQuery):(Input.point q).encode∈language ↔(Input.point q).encode∈pointLanguage:=by
  have HP:Input.IsPoint (Input.point q).encode:=(Input.isPoint_iff _).mpr ⟨q,rfl⟩
  change (PointInput (Input.point q).encode∧WellFormed (Input.point q).encode∧
    (Input.point q).encode∈EndpointValidation.validEndpointLanguage∧Holds (Input.point q).encode)↔_
  simp only [PointInput,HP,true_and,WellFormed,CanonicalEndpointNative.description_point,EndpointValidation.validEndpoint_encode]
  constructor
  · rintro ⟨hd,HE,HH⟩
    exact (holds_point_iff q hd HE).mp HH
  · intro H
    obtain ⟨hd,x,y,HX,HY,_⟩:=(point_encode_mem_iff q).mp H
    have HE:=(And.intro (Exists.intro x HX) (Exists.intro y HY))
    exact ⟨hd,HE,(holds_point_iff q hd HE).mpr H⟩

theorem language_eq_point:language=pointLanguage:=by
  ext c
  by_cases hp:Input.IsPoint c
  · obtain ⟨q,rfl⟩:=(Input.isPoint_iff c).mp hp
    exact language_point_iff q
  · have HN:c∉pointLanguage:=by
      rintro ⟨q,rfl,_⟩
      exact hp ((Input.isPoint_iff _).mpr ⟨q,rfl⟩)
    exact iff_of_false (fun H=>hp H.1) HN
include D in
theorem point_mem_PSPACE:pointLanguage∈PSPACE:=by
  rw [←language_eq_point]
  exact mem_PSPACE D
end LeanCanny.Connectivity.CanonicalAuxiliaryNativePointSearch
