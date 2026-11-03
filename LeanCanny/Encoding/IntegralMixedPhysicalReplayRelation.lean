/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalReplayThom
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedValidity
public import LeanCanny.Encoding.IntegralMixedMarkedReplayRelation

/-! # One full marked replay retains its literal original candidate

Marked membership, every original leaf and the Thom comparison refer to one
complete physical tuple. Physical correlation/frame predicates can be added
to this relation without changing either sampled context or vertex word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalReplayRelation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  bank tables
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable def language : Language := {q |
  q∈IntegralMixedPhysicalReplayThom.language hn ht ha hR outer ∧
  q∈IntegralMixedPhysicalMarkedTest.language hn ht ha hR outer}

theorem decider (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceDecider (language hn ht ha hR outer) := by
  have A:=(IntegralMixedPhysicalReplayThom.decider hn ht ha hR outer ER).flagEvaluator
  have B:=(IntegralMixedPhysicalMarkedTest.decider hn ht ha hR outer ER).flagEvaluator
  apply (A.andFlags B).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem thom_fields (q ctx w : List Bool)
    (hc : IntegralMixedPhysicalReplayThom.context q=ctx) (hw : IntegralMixedPhysicalReplayThom.word q=w) :
    q∈IntegralMixedPhysicalReplayThom.language hn ht ha hR outer ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
      ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
        ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
          IntegralMixedPhysicalReplayNew.point hn ht ha hR outer ctx w hv i := by
  cases hc
  cases hw
  exact IntegralMixedPhysicalReplayThom.language_iff hn ht ha hR outer q

theorem thom_packet (ctx w : List Bool) :
    pair ctx w∈IntegralMixedPhysicalReplayThom.language hn ht ha hR outer ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
      ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
        ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
          IntegralMixedPhysicalReplayNew.point hn ht ha hR outer ctx w hv i :=
  thom_fields hn ht ha hR outer _ ctx w (pairFst_pair _ _) (pairSnd_pair _ _)

theorem point_original (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) (i : Fin (number n ctx)) :
    IntegralMixedPhysicalMarkedSemantics.point hn ht ha hR outer ctx w hv (i.castAdd 4)=
      IntegralMixedPhysicalReplayNew.point hn ht ha hR outer ctx w hv i := by
  have HC:=IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha hR outer ctx
  simp only [IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair] at HC
  change number n ctx+(if outer then 10 else 8)≤IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx) at HC
  have HI : i.val<IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx):=by have HJ:=i.isLt;omega
  have HE:=IntegralFramedPhysicalBankTerm.env_coordinate (bank hn ht ha hR outer) (tables hn ht ha hR outer)
    (represents hn ht ha hR outer) (sampleContext ctx) w hv i.val HI
  have HX : IntegralFramedPhysicalIntegerLeaves.coordinate
      (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive (sampleContext ctx) (BinaryNatCode.encode i.val)=
      IntegralMixedPhysicalReplayNew.coordinate hn ht ha hR outer (sampleContext ctx)
        (IntegralMixedCandidateReplayDatum.packet (pairFst ctx) i.val 0) :=by
    apply Fin.ext
    rw [IntegralMixedPhysicalReplayNew.coordinate_packet]
    simp only [IntegralFramedPhysicalIntegerLeaves.coordinate,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rfl
  rw [HX] at HE
  exact HE

theorem projection_eq (ctx w : List Bool)
    (hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (z : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (IntegralMixedMarkedPointTest.charge t ctx) (IntegralMixedMarkedPointTest.charge t ctx) (R ctx))
    (hz : z.val.val=IntegralMixedPhysicalMarkedSemantics.point hn ht ha hR outer ctx w hv)
    (he : ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp i=
      IntegralMixedPhysicalReplayNew.point hn ht ha hR outer ctx w hv i) :
    (BoundedRegularSource.markedProjection _ _ _ _ z).val=IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp := by
  funext i
  rw [BoundedRegularSource.markedProjection_apply,hz]
  exact (point_original hn ht ha hR outer ctx w hv i).trans (he i).symm

theorem sound (ctx w : List Bool) (h : pair ctx w∈language hn ht ha hR outer) :
    IntegralMixedMarkedReplayRelation.originalZero hn ht ha (pairFst ctx) := by
  obtain ⟨hp,_,he⟩:=(thom_packet hn ht ha hR outer ctx w).mp h.1
  obtain ⟨hv,_,z,hz⟩:=(IntegralMixedPhysicalMarkedValidity.accepted_iff hn ht ha hR outer ctx w).mp h.2
  have HP:=projection_eq hn ht ha hR outer ctx w hp hv z hz he
  have HZ:=(BoundedRegularSource.markedProjection _ _ _ _ z).property.1
  rw [HP] at HZ
  exact ⟨hp,(Term.eval_finitePolynomial _ _ _).symm.trans HZ⟩

theorem accepted_good (u label metadata w : List Bool)
    (h : pair (pair (pair u label) metadata) w∈language hn ht ha hR outer) :
    LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label := by
  have H:=sound hn ht ha hR outer (pair (pair u label) metadata) w h
  have HC : pairFst (pair (pair u label) metadata)=pair u label:=pairFst_pair _ _
  exact (IntegralMixedMarkedReplayRelation.originalZero_packet hn ht ha u label).mp
    (Eq.mp (congrArg (IntegralMixedMarkedReplayRelation.originalZero hn ht ha) HC) H)

theorem mem_PSPACE (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    language hn ht ha hR outer∈PSPACE :=(decider hn ht ha hR outer ER).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalReplayRelation
