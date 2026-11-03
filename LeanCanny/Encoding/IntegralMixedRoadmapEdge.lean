/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapIdentityReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
/-! # Actual native roadmap adjacency

An edge compares entire atomic points or pairs two guarded proper incidences
whose captured midpoint signatures agree. No ancestry edge is inserted.
Geometric soundness of the second case and global completeness are separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def Proper (z : List Bool):=IntegralMixedRoadmapIdentity.SameCandidate z∧
  IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 (pairFst z)∧
  IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 (pairSnd z)∧
  z∈IntegralMixedRoadmapProperMidSignature.language hn ht ha hR0

noncomputable def language : Language:={z |z∈IntegralMixedRoadmapIdentity.language hn ht ha hR0∨Proper hn ht ha hR0 z}
noncomputable def Adjacent (a b : List Bool):=pair a b∈language hn ht ha hR0

theorem proper_evaluator : SpaceFunction (fun z=>[decide (Proper hn ht ha hR0 z)]):=by
  have EC:=SpaceFunction.ofFP _ IntegralMixedRoadmapIdentity.sameCandidate_FP.flag_mem_FP
  have EL:=(IntegralMixedRoadmapLocalEdge.evaluator hn ht ha hR0).precompose pairFst pairFst_mem_FP
  have ER:=(IntegralMixedRoadmapLocalEdge.evaluator hn ht ha hR0).precompose pairSnd pairSnd_mem_FP
  have EM:=(IntegralMixedRoadmapProperMidSignature.decider hn ht ha hR0).flagEvaluator
  exact (EC.andFlags (EL.andFlags (ER.andFlags EM))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Proper,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

theorem evaluator : SpaceFunction (fun z=>[decide (z∈language hn ht ha hR0)]):=by
  have EI:=(IntegralMixedRoadmapIdentity.decider hn ht ha hR0).flagEvaluator
  have EP:=proper_evaluator hn ht ha hR0
  have HOr:=(Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  exact ((EI.pairOutputs EP).postcompose _ HOr.flag_mem_FP).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language hn ht ha hR0):=by
  apply (evaluator hn ht ha hR0).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [List.cons.injEq,and_true,decide_eq_true_eq]

theorem of_same_point (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b)
    (hp : HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 a hA)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 b hB)) : Adjacent hn ht ha hR0 a b :=
  Or.inl ((IntegralMixedRoadmapIdentity.language_iff hn ht ha hR0 a b hA hB hc).mpr hp)

theorem refl (a : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a) :
    Adjacent hn ht ha hR0 a a:=of_same_point hn ht ha hR0 a a hA hA rfl HEq.rfl

theorem valid (a b : List Bool) (h : Adjacent hn ht ha hR0 a b) :
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a∧IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b :=by
  rcases h with HI|HP
  · have H:=HI.2
    simpa only [IntegralMixedRoadmapIdentity.left,IntegralMixedRoadmapIdentity.right,pairFst_pair,pairSnd_pair] using
      And.intro H.1 H.2.1
  · simpa only [pairFst_pair,pairSnd_pair] using And.intro HP.2.1.1 HP.2.2.1.1

theorem candidate_eq (a b : List Bool) (h : Adjacent hn ht ha hR0 a b) :
    IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b :=by
  rcases h with HI|HP
  · simpa only [IntegralMixedRoadmapIdentity.SameCandidate,IntegralMixedRoadmapIdentity.left,
      IntegralMixedRoadmapIdentity.right,pairFst_pair,pairSnd_pair] using HI.1
  · simpa only [IntegralMixedRoadmapIdentity.SameCandidate,IntegralMixedRoadmapIdentity.left,
      IntegralMixedRoadmapIdentity.right,pairFst_pair,pairSnd_pair] using HP.1

end LeanCanny.Encoding.IntegralMixedRoadmapEdge
