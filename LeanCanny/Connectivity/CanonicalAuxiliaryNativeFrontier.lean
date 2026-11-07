/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryFrontierJointCodec
public import LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
public import LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibility
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecision
/-! # The original bit-frontier graph has an exact native edge test

Only the constructive guarded-feasibility decider is a lower cost parameter.
The graph and its geometric meaning are the literal original cover.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryNativeFrontier
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leftQuery (q:List Bool):=pair (pairFst q) (pairFst (pairSnd q))
def rightQuery (q:List Bool):=pair (pairFst q) (pairSnd (pairSnd q))
def reverse (q:List Bool):=pair (pairFst q) (pair (pairSnd (pairSnd q)) (pairFst (pairSnd q)))
theorem leftQuery_FP:leftQuery∈FP:=by polytime [leftQuery]
theorem rightQuery_FP:rightQuery∈FP:=by polytime [rightQuery]
theorem reverse_FP:reverse∈FP:=by polytime [reverse]
noncomputable def Holds (q:List Bool):Prop:=CanonicalAuxiliaryCandidateLabels.Valid (leftQuery q) ∧
  CanonicalAuxiliaryCandidateLabels.Valid (rightQuery q) ∧
  (q∈LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ∨
    q∈FormulaSignSlotRadialGuardedFeasibility.language ∨reverse q∈FormulaSignSlotRadialGuardedFeasibility.language)
noncomputable def edge (original a b:List Bool):Bool:=decide (Holds (pair original (pair a b)))
noncomputable def width:=CanonicalAuxiliaryCandidateCover.tagWidth
noncomputable def valid:=CanonicalAuxiliaryBitFrontier.valid

variable (D:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.language)
include D in
theorem evaluator:SpaceFunction (fun q=>[decide (Holds q)]):=by
  have EL:=CanonicalAuxiliaryCandidateLabels.decider.flagEvaluator.precompose leftQuery leftQuery_FP
  have ER:=CanonicalAuxiliaryCandidateLabels.decider.flagEvaluator.precompose rightQuery rightQuery_FP
  have EQ:=LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.decider.flagEvaluator
  have EF:=D.flagEvaluator
  have EB:=D.flagEvaluator.precompose reverse reverse_FP
  exact IntegralPolynomialWindowTarskiDecision.flag_and _ _ EL
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ ER
      (IntegralPolynomialWindowTarskiDecision.flag_or _ _ EQ (IntegralPolynomialWindowTarskiDecision.flag_or _ _ EF EB)))

include D in
theorem edge_computable:ComputableTidilyInPolySpace
    (fun p:List Bool×List Bool×List Bool=>edge p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool:=by
  have EQ:=pair_computable (ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits))
    (pair_computable (ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)).fst'
      (ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)).snd')
  have E:=(evaluator D).computable.comp (.of_polyTime EQ)
  obtain ⟨T,S,hS,h⟩:=E
  exact ⟨T,S,hS,h.of_enc_eq (fun p=>rfl)⟩
theorem valid_computable:ComputableTidilyInPolySpace
    (fun p:List Bool×List Bool=>valid p.1 p.2) (encPair encBits encBits) encBool:=
  CanonicalAuxiliaryBitFrontier.vertex_computable
theorem width_unary:UnaryFn width:=CanonicalAuxiliaryCandidateCover.tagWidth_unary

private theorem valid_length (d:Description) (a:List Bool)
    (ha:CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) a)):
    a.length=CanonicalAuxiliaryBitFrontier.width d:=by
  simpa only [pairSnd_pair,pairFst_pair,CanonicalAuxiliaryBitFrontier.width] using ha.1.1

private theorem edge_encoded_iff (d:Description) (hd:d.WellFormed) (i j:CanonicalAuxiliaryCandidateCover.Index d):
    edge (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i)
      (CanonicalAuxiliaryCandidateCover.encode d j)=true ↔CanonicalAuxiliaryCandidateCover.edge d i j:=by
  unfold edge Holds
  simp only [decide_eq_true_eq,leftQuery,rightQuery,reverse,pairFst_pair,pairSnd_pair]
  change (_∧_∧(CanonicalAuxiliaryJointHeader.header d i j∈LeanCanny.Encoding.FormulaSignSlotProjectedSampleEquality.language ∨
    CanonicalAuxiliaryJointHeader.header d i j∈FormulaSignSlotRadialGuardedFeasibility.language ∨
    CanonicalAuxiliaryJointHeader.header d j i∈FormulaSignSlotRadialGuardedFeasibility.language))↔_
  rw [FormulaSignSlotRadialGuardedFeasibility.language_iff_feasible,
    FormulaSignSlotRadialGuardedFeasibility.language_iff_feasible,←CanonicalAuxiliaryFrontierJointCodec.edge_iff d hd i j]
  constructor
  · exact fun H=>H.2.2
  · intro H
    have HN:=FrontierCover.Incident.nonempty (CanonicalAuxiliaryCandidateCover.piece d) H
    exact ⟨(CanonicalAuxiliaryCandidateLabels.encoded_nonempty_iff d hd i).mp HN.1,
      (CanonicalAuxiliaryCandidateLabels.encoded_nonempty_iff d hd j).mp HN.2,H⟩

theorem edge_eq (d:Description) (hd:d.WellFormed) (a b:List Bool):
    edge (CanonicalSignRefinement.original d) a b=CanonicalAuxiliaryBitFrontier.edge d a b:=by
  apply Bool.eq_iff_iff.mpr
  by_cases hv:CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) a) ∧
      CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) b)
  · obtain ⟨ha,hb⟩:=hv
    let i:=CanonicalAuxiliaryCandidateLabels.decode d a ha
    let j:=CanonicalAuxiliaryCandidateLabels.decode d b hb
    have HA:=valid_length d a ha
    have HB:=valid_length d b hb
    have HE:=edge_encoded_iff d hd i j
    rw [CanonicalAuxiliaryCandidateLabels.encode_decode d a ha,CanonicalAuxiliaryCandidateLabels.encode_decode d b hb] at HE
    rw [HE]
    simp only [CanonicalAuxiliaryBitFrontier.edge,dite_eq_left HA,dite_eq_left HB,decide_eq_true_eq]
    change FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.piece d) i j ↔ _
    unfold FrontierCover.Incident
    simp only [CanonicalAuxiliaryBitFrontier.piece,dite_eq_left ha,dite_eq_left hb]
    rfl
  · have HFalse:edge (CanonicalSignRefinement.original d) a b≠true:=by
      intro H
      have HT:Holds (pair (CanonicalSignRefinement.original d) (pair a b)):=of_decide_eq_true H
      apply hv
      exact ⟨by simpa only [leftQuery,pairFst_pair,pairSnd_pair] using HT.1,
        by simpa only [rightQuery,pairFst_pair,pairSnd_pair] using HT.2.1⟩
    have HOld:CanonicalAuxiliaryBitFrontier.edge d a b≠true:=by
      unfold CanonicalAuxiliaryBitFrontier.edge
      split_ifs with hA hB
      · intro H0
        have H:=of_decide_eq_true H0
        have HN:=H.nonempty _
        exact hv ⟨(CanonicalAuxiliaryBitFrontier.piece_nonempty_iff d hd ⟨a,hA⟩).mp HN.1,
          (CanonicalAuxiliaryBitFrontier.piece_nonempty_iff d hd ⟨b,hB⟩).mp HN.2⟩
      all_goals exact Bool.false_ne_true
    exact iff_of_false HFalse HOld
end LeanCanny.Connectivity.CanonicalAuxiliaryNativeFrontier
