/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderAssociation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedAnchor
/-! # Native association with independently validated own-marker paths

Both depth-zero seeds carry actual paths to own marked-point vertices. The
markers have no depth restriction. No point attachment is inferred from Valid.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredAssociation
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FormulaSignSlotRadialProviderAssociation (left right provider)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def base (q : List Bool) :=pairFst (pairFst q)
def oldMarker (q : List Bool) :=IntegralMixedRoadmapWordLabel.decode (pairSnd (pairFst q))
def externalMarker (q : List Bool) :=IntegralMixedRoadmapWordLabel.decode (pairSnd q)
def externalProvider (z : List Bool) :=FormulaSignSlotRadialProviderAtomic.provider (right z)
theorem base_FP : base∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem oldMarker_FP : oldMarker∈FP:=mem_FP_comp
  (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) IntegralMixedRoadmapWordLabel.decode_FP
theorem externalMarker_FP : externalMarker∈FP:=mem_FP_comp pairSnd_mem_FP IntegralMixedRoadmapWordLabel.decode_FP
theorem externalProvider_FP : externalProvider∈FP:=mem_FP_comp
  FormulaSignSlotRadialProviderAssociation.right_FP FormulaSignSlotRadialProviderAtomic.provider_FP

def oldReachQuery (q : List Bool) :=FormulaSignSlotRadialProviderAssociation.reachQuery
  (pair (base q) (pairSnd (pairFst q)))
def externalReachQuery (q : List Bool) :=FormulaSignSlotRadialProviderAssociation.reachQuery
  (pair (pair (right (base q)) []) (pairSnd q))
theorem oldReachQuery_FP : oldReachQuery∈FP:=mem_FP_comp
  (mem_FP_pair base_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  FormulaSignSlotRadialProviderAssociation.reachQuery_FP
theorem externalReachQuery_FP : externalReachQuery∈FP:=mem_FP_comp
  (mem_FP_pair (mem_FP_pair (mem_FP_comp base_FP FormulaSignSlotRadialProviderAssociation.right_FP)
    (constFn_mem_FP [])) pairSnd_mem_FP) FormulaSignSlotRadialProviderAssociation.reachQuery_FP

theorem oldReachQuery_packet (z oldBits extBits : List Bool) :
    oldReachQuery (pair (pair z oldBits) extBits)=pair (provider z)
      (pair (left z) (IntegralMixedRoadmapWordLabel.decode oldBits)) := by
  simp only [oldReachQuery,FormulaSignSlotRadialProviderAssociation.reachQuery,
    FormulaSignSlotRadialProviderAssociation.witness,base,pairFst_pair,pairSnd_pair]
theorem externalReachQuery_packet (z oldBits extBits : List Bool) :
    externalReachQuery (pair (pair z oldBits) extBits)=pair (externalProvider z)
      (pair (right z) (IntegralMixedRoadmapWordLabel.decode extBits)) := by
  simp only [externalReachQuery,FormulaSignSlotRadialProviderAssociation.reachQuery,
    FormulaSignSlotRadialProviderAssociation.witness,provider,left,externalProvider,base,pairFst_pair,pairSnd_pair]

noncomputable def witnessLanguage : Language := {q |
  oldReachQuery q∈FormulaSignSlotRadialProviderGraph.nativeReachLanguage ∧
  externalReachQuery q∈FormulaSignSlotRadialProviderGraph.nativeReachLanguage ∧
  oldMarker q∈FormulaSignSlotRadialProviderMarkedAnchor.language ∧
  externalMarker q∈FormulaSignSlotRadialProviderMarkedAnchor.language}

theorem witness_decider : SpaceDecider witnessLanguage := by
  have EO := (FormulaSignSlotRadialProviderGraph.native_reach_decider.precompose oldReachQuery oldReachQuery_FP).flagEvaluator
  have EE := (FormulaSignSlotRadialProviderGraph.native_reach_decider.precompose externalReachQuery externalReachQuery_FP).flagEvaluator
  have MO := (FormulaSignSlotRadialProviderMarkedAnchor.decider.precompose oldMarker oldMarker_FP).flagEvaluator
  have ME := (FormulaSignSlotRadialProviderMarkedAnchor.decider.precompose externalMarker externalMarker_FP).flagEvaluator
  apply (EO.andFlags (EE.andFlags (MO.andFlags ME))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def oldWidth (z : List Bool) :=FormulaSignSlotRadialProviderGraph.width (provider z)
noncomputable def externalWidth (z : List Bool) :=FormulaSignSlotRadialProviderGraph.width (externalProvider z)
theorem oldWidth_unary : UnaryFn oldWidth:=FormulaSignSlotRadialProviderGraph.width_unary.comp
  FormulaSignSlotRadialProviderAssociation.provider_FP
theorem externalWidth_unary : UnaryFn externalWidth:=FormulaSignSlotRadialProviderGraph.width_unary.comp externalProvider_FP
noncomputable def BoundedMarkers (z : List Bool) : Prop :=∃oldBits : List Bool,
  oldBits.length=oldWidth z ∧∃extBits : List Bool,extBits.length=externalWidth z ∧
    pair (pair z oldBits) extBits∈witnessLanguage

theorem boundedMarkers_evaluator : SpaceFunction (fun z=>[decide (BoundedMarkers z)]) := by
  have E := witness_decider.flagEvaluator.exists_words (externalWidth_unary.comp pairFst_mem_FP)
  exact (E.exists_words oldWidth_unary).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [BoundedMarkers,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def Markers (a ext : List Bool) : Prop :=∃mOld mExt,
  FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider a) a mOld ∧
  FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider ext) ext mExt ∧
  mOld∈FormulaSignSlotRadialProviderMarkedAnchor.language ∧mExt∈FormulaSignSlotRadialProviderMarkedAnchor.language

noncomputable def Anchored (a ext : List Bool) : Prop :=
  FormulaSignSlotRadialProviderAssociation.Associated a ext∧Markers a ext

theorem marker_byte_bounds (a ext mOld mExt : List Bool)
    (hOld : FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider a) a mOld)
    (hExt : FormulaSignSlotRadialProviderGraph.RawReachable (FormulaSignSlotRadialProviderAtomic.provider ext) ext mExt) :
    mOld.length≤FormulaSignSlotRadialProviderAtomic.providerVertexBudget (FormulaSignSlotRadialProviderAtomic.provider a) ∧
    mExt.length≤FormulaSignSlotRadialProviderAtomic.providerVertexBudget (FormulaSignSlotRadialProviderAtomic.provider ext) :=
  ⟨FormulaSignSlotRadialProviderAssociation.witness_byte_bound a mOld hOld,
    FormulaSignSlotRadialProviderAssociation.witness_byte_bound ext mExt hExt⟩

theorem boundedMarkers_iff (z : List Bool) : BoundedMarkers z↔Markers (left z) (right z) := by
  constructor
  · rintro ⟨oldBits,_,extBits,_,HO,HE,MO,ME⟩
    refine ⟨IntegralMixedRoadmapWordLabel.decode oldBits,IntegralMixedRoadmapWordLabel.decode extBits,?_,?_,?_,?_⟩
    · simpa only [oldReachQuery_packet,FormulaSignSlotRadialProviderGraph.nativeReachLanguage,
        FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,
        Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,provider] using HO
    · simpa only [externalReachQuery_packet,FormulaSignSlotRadialProviderGraph.nativeReachLanguage,
        FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,
        Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,externalProvider] using HE
    · simpa only [oldMarker,pairFst_pair,pairSnd_pair] using MO
    · simpa only [externalMarker,pairSnd_pair] using ME
  · rintro ⟨mOld,mExt,HO,HE,MO,ME⟩
    obtain ⟨HBO,HBE⟩ := marker_byte_bounds (left z) (right z) mOld mExt HO HE
    let oldBits := IntegralMixedRoadmapWordLabel.encode
      (FormulaSignSlotRadialProviderAtomic.providerVertexBudget (provider z)) mOld
    let extBits := IntegralMixedRoadmapWordLabel.encode
      (FormulaSignSlotRadialProviderAtomic.providerVertexBudget (externalProvider z)) mExt
    refine ⟨oldBits,IntegralMixedRoadmapWordLabel.encode_length _ mOld HBO,
      extBits,IntegralMixedRoadmapWordLabel.encode_length _ mExt HBE,?_,?_,?_,?_⟩
    · simpa only [oldReachQuery_packet,FormulaSignSlotRadialProviderGraph.nativeReachLanguage,
        FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,
        Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,oldBits,IntegralMixedRoadmapWordLabel.decode_encode,provider] using HO
    · simpa only [externalReachQuery_packet,FormulaSignSlotRadialProviderGraph.nativeReachLanguage,
        FormulaSignSlotRadialProviderGraph.leftLabel,FormulaSignSlotRadialProviderGraph.rightLabel,
        Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,extBits,IntegralMixedRoadmapWordLabel.decode_encode,externalProvider] using HE
    · simpa only [oldMarker,pairFst_pair,pairSnd_pair,oldBits,IntegralMixedRoadmapWordLabel.decode_encode] using MO
    · simpa only [externalMarker,pairSnd_pair,extBits,IntegralMixedRoadmapWordLabel.decode_encode] using ME

noncomputable def language : Language :={z |z∈FormulaSignSlotRadialProviderAssociation.language ∧BoundedMarkers z}

theorem decider : SpaceDecider language := by
  apply (FormulaSignSlotRadialProviderAssociation.decider.flagEvaluator.andFlags boundedMarkers_evaluator).decider
    (fun v=>decide (v=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language∈PSPACE:=decider.mem_PSPACE

theorem language_iff (a ext : List Bool) : pair a ext∈language↔Anchored a ext := by
  change (pair a ext∈FormulaSignSlotRadialProviderAssociation.language ∧BoundedMarkers (pair a ext))↔_
  rw [FormulaSignSlotRadialProviderAssociation.language_iff,boundedMarkers_iff]
  simp only [Anchored,left,right,pairFst_pair,pairSnd_pair]

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderAnchoredAssociation
