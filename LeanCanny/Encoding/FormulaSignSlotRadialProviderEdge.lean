/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderLocalEdge
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
/-! # Actual native roadmap adjacency

An edge compares entire atomic points or pairs two guarded proper incidences
whose captured midpoint signatures agree within one literal provider. No ancestry edge is inserted.
Geometric soundness of the second case and global completeness are separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Proper (z : List Bool):=FormulaSignSlotRadialProviderIdentity.SameProvider z∧
  FormulaSignSlotRadialProviderLocalEdge.Local (pairFst z)∧
  FormulaSignSlotRadialProviderLocalEdge.Local (pairSnd z)∧
  z∈FormulaSignSlotRadialProviderProperMidSignature.language

noncomputable def language : Language:={z |z∈FormulaSignSlotRadialProviderIdentity.language∨Proper z}
noncomputable def Adjacent (a b : List Bool):=pair a b∈language

theorem proper_evaluator : SpaceFunction (fun z=>[decide (Proper z)]):=by
  have EC:=SpaceFunction.ofFP _ FormulaSignSlotRadialProviderIdentity.sameProvider_FP.flag_mem_FP
  have EL:=(FormulaSignSlotRadialProviderLocalEdge.evaluator).precompose pairFst pairFst_mem_FP
  have ER:=(FormulaSignSlotRadialProviderLocalEdge.evaluator).precompose pairSnd pairSnd_mem_FP
  have EM:=(FormulaSignSlotRadialProviderProperMidSignature.decider).flagEvaluator
  exact (EC.andFlags (EL.andFlags (ER.andFlags EM))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Proper,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

theorem evaluator : SpaceFunction (fun z=>[decide (z∈language)]):=by
  have EI:=(FormulaSignSlotRadialProviderIdentity.decider).flagEvaluator
  have EP:=proper_evaluator
  have HOr:=(Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  exact ((EI.pairOutputs EP).postcompose _ HOr.flag_mem_FP).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language):=by
  apply (evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [List.cons.injEq,and_true,decide_eq_true_eq]

theorem of_same_point (a b : List Bool) (hA : FormulaSignSlotRadialProviderAtomic.Valid a)
    (hB : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hc : FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b)
    (hp : HEq (FormulaSignSlotRadialProviderIdentity.point a hA)
      (FormulaSignSlotRadialProviderIdentity.point b hB)) : Adjacent a b :=
  Or.inl ((FormulaSignSlotRadialProviderIdentity.language_iff a b hA hB hc).mpr hp)

theorem refl (a : List Bool) (hA : FormulaSignSlotRadialProviderAtomic.Valid a) :
    Adjacent a a:=of_same_point a a hA hA rfl HEq.rfl

theorem valid (a b : List Bool) (h : Adjacent a b) :
    FormulaSignSlotRadialProviderAtomic.Valid a∧FormulaSignSlotRadialProviderAtomic.Valid b :=by
  rcases h with HI|HP
  · have H:=HI.2
    simpa only [FormulaSignSlotRadialProviderIdentity.left,FormulaSignSlotRadialProviderIdentity.right,pairFst_pair,pairSnd_pair] using
      And.intro H.1 H.2.1
  · simpa only [pairFst_pair,pairSnd_pair] using And.intro HP.2.1.1 HP.2.2.1.1

theorem provider_eq (a b : List Bool) (h : Adjacent a b) :
    FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b :=by
  rcases h with HI|HP
  · simpa only [FormulaSignSlotRadialProviderIdentity.SameProvider,FormulaSignSlotRadialProviderIdentity.left,
      FormulaSignSlotRadialProviderIdentity.right,pairFst_pair,pairSnd_pair] using HI.1
  · simpa only [FormulaSignSlotRadialProviderIdentity.SameProvider,FormulaSignSlotRadialProviderIdentity.left,
      FormulaSignSlotRadialProviderIdentity.right,pairFst_pair,pairSnd_pair] using HP.1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
