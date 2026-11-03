/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReplayCompleteness

/-! # A native marked replay relation and its original zero-set soundness -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReplayRelation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original)
open IntegralMixedAuxiliaryMarkedNativeVertex (input)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.parameters
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.input
  IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

noncomputable def language : Language := {q |
  q∈IntegralMixedCandidateReplayThom.language hn ht ha hR ∧
  q∈IntegralMixedMarkedPointTest.language hn ht ha hR}

theorem decider : SpaceDecider (language hn ht ha hR) := by
  have L:=(IntegralMixedCandidateReplayThom.decider hn ht ha hR).flagEvaluator
  have M:=(IntegralMixedMarkedPointTest.decider hn ht ha hR).flagEvaluator
  apply (L.andFlags M).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language hn ht ha hR∈PSPACE := (decider hn ht ha hR).mem_PSPACE

theorem original_coordinate (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (i : Fin (number n ctx)) :
    IntegralMixedMarkedPointReadback.point hn ht ha hR ctx w hv (i.castAdd 4)=
      IntegralMixedCandidateReplayNew.point hn ht ha hR ctx w hv i :=
  IntegralMixedMarkedPointReadback.coordinate hn ht ha hR ctx w hv i.val (by omega)

theorem projection_eq (ctx w : List Bool)
    (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (z : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (IntegralMixedMarkedPointTest.charge t ctx) (IntegralMixedMarkedPointTest.charge t ctx) (R ctx))
    (hz : z.val.val=IntegralMixedMarkedPointReadback.point hn ht ha hR ctx w hv)
    (he : ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp i=
      IntegralMixedCandidateReplayNew.point hn ht ha hR ctx w hv i) :
    (BoundedRegularSource.markedProjection _ _ _ _ z).val=IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp := by
  funext i
  rw [BoundedRegularSource.markedProjection_apply,hz]
  exact (original_coordinate hn ht ha hR ctx w hv i).trans (he i).symm

theorem sound (ctx w : List Bool) (h : pair ctx w∈language hn ht ha hR) :
    ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx),
      (t (original ctx)).eval (Formula.extend (IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp))=0 := by
  obtain ⟨hp,hv,HE⟩:=(IntegralMixedAuxiliaryMarkedThomCompleteness.packet_iff hn ht ha hR ctx w).mp h.1
  obtain ⟨hv',_,z,hz⟩:=(IntegralMixedMarkedReplayValidity.accepted_iff hn ht ha hR ctx w).mp h.2
  have HX:=projection_eq hn ht ha hR ctx w hp hv' z hz HE
  refine ⟨hp,?_⟩
  have HZ:=(BoundedRegularSource.markedProjection _ _ _ _ z).property.1
  rw [HX] at HZ
  exact (Term.eval_finitePolynomial _ _ _).symm.trans HZ

noncomputable def originalZero (q : List Bool) : Prop :=
  ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha q,
    (t (pairFst q)).eval (Formula.extend (IntegralMixedAuxiliaryCandidate.point hn ht ha q hp))=0

theorem sound_original (ctx w : List Bool) (h : pair ctx w∈language hn ht ha hR) :
    originalZero hn ht ha (candidate ctx) := sound hn ht ha hR ctx w h

theorem extend_cast {a b : ℕ} (h : a=b) (f : Fin a→ℝ) :
    Formula.extend (f∘Fin.cast h.symm)=Formula.extend f := by
  cases h
  rfl

theorem pointAt_extend (u label : List Bool)
    (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label)) :
    Formula.extend (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label hp)=
      Formula.extend (IntegralMixedAuxiliaryCandidate.point hn ht ha (pair u label) hp) :=
  extend_cast (congrArg n (pairFst_pair u label)) (IntegralMixedAuxiliaryCandidate.point hn ht ha (pair u label) hp)

theorem originalZero_packet (u label : List Bool) :
    originalZero hn ht ha (pair u label) ↔LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label := by
  have HE (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pair u label)) :
      (t (pairFst (pair u label))).eval (Formula.extend (IntegralMixedAuxiliaryCandidate.point hn ht ha (pair u label) hp))=
        (t u).eval (Formula.extend (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label hp)) :=
    (congrArg (fun T : Term=>T.eval (Formula.extend (IntegralMixedAuxiliaryCandidate.point hn ht ha (pair u label) hp)))
      (congrArg t (pairFst_pair u label))).trans
      (congrArg (fun e : ℕ→ℝ=>(t u).eval e) (pointAt_extend hn ht ha u label hp).symm)
  constructor
  · rintro ⟨hp,hp0⟩
    exact ⟨hp,(HE hp).symm.trans hp0⟩
  · rintro ⟨hp,hp0⟩
    exact ⟨hp,(HE hp).trans hp0⟩

theorem exists_accepted (u label outer : List Bool)
    (hg : LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer)) :
    ∃w : List Bool,w.length=SquareSampleCompleteVertices.width (input hn ht ha hR)
      (sampleContext (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer)) ∧
      pair (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer) w∈language hn ht ha hR := by
  obtain ⟨w,hlen,hT,hM⟩:=IntegralMixedMarkedReplayCompleteness.exists_accepted hn ht ha hR u label outer hg hLower
  exact ⟨w,hlen,hT,hM⟩

theorem good_iff_exists (u label outer : List Bool)
    (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer)) :
    LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label ↔
      ∃w : List Bool,w.length=SquareSampleCompleteVertices.width (input hn ht ha hR)
        (sampleContext (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer)) ∧
        pair (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer) w∈language hn ht ha hR := by
  constructor
  · exact fun hg=>exists_accepted hn ht ha hR u label outer hg hLower
  · rintro ⟨w,_,hw⟩
    have H:=sound_original hn ht ha hR (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer) w hw
    have HC : candidate (IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer)=pair u label := by
      simp only [candidate,IntegralMixedAuxiliaryMarkedCandidateAtRadius.context,pairFst_pair]
    exact (originalZero_packet hn ht ha u label).mp (Eq.mp (congrArg (originalZero hn ht ha) HC) H)

end LeanCanny.Encoding.IntegralMixedMarkedReplayRelation
