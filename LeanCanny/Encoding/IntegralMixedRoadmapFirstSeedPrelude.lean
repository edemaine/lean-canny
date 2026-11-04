/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCandidateRealization
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedRealization
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedLayout
/-! # Prescribed original roots at the actual full seed horizon -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem integer_commands {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (N :ℕ) (p :Fin N→Polynomial ℤ) (hp :∀i,p i≠0) (hd :∀i,(p i).natDegree≤2^B)
    (room :N≤S+1) :
    IntegralMixedCausalPlanBits.commands initial
      (List.ofFn (fun i :Fin N=>(⟨Q,hQ,.integer (p i) (hp i) (hd i)⟩ :Record n B)))
      (by simpa only [List.length_ofFn] using room)=
      List.ofFn (fun i :Fin N=>(⟨Q,hQ,.integer (p i) (hp i) (hd i)⟩ :Instruction n B)):=by
  induction N with
  | zero=>rfl
  | succ N ih=>
    simp only [List.ofFn_succ,IntegralMixedCausalPlanBits.commands_cons]
    apply congrArg₂ List.cons
    · rfl
    · exact ih (fun i=>p i.succ) (fun i=>hp i.succ) (fun i=>hd i.succ) (by omega)

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryCandidate.bankData IntegralMixedAuxiliaryParameters.parameters
  IntegralMixedAuxiliaryParameters.scalarWidth IntegralMixedAuxiliaryParameters.scalarCeiling
  IntegralMixedAuxiliaryParameters.spatialDegree IntegralMixedAuxiliaryParameters.augmented
  IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedFramedHistoryFamilyBits.family SquareSampleCompleteVertices.candidate
  IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedMarkedRecordContinuation.oldCommands IntegralMixedMarkedRecordContinuation.records_before
  IntegralMixedCausalRecordPlanBits.count IntegralMixedCausalRecordPlanBits.records
  IntegralMixedFramedHistoryScript.Index

private theorem initial_records (root :List Bool) :
    IntegralMixedMarkedRecordContinuation.records_before hn ht ha hR0 root 0=
      IntegralMixedStaticRecordPrefix.originals (Q root)
        (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root) (number n root+8)
        (IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root)
        (IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root)
        (IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root):=by
  unfold IntegralMixedMarkedRecordContinuation.records_before IntegralMixedStaticRecordContinuation.prefixRecords
  rw [IntegralMixedStaticRecordPrefix.prefix_form _ _ _ _ _ _ _ _ _ 0 (Nat.zero_le _)]
  simp only [List.range_zero,List.map_nil,List.append_nil,List.reverse_reverse]

private theorem target_width : (P).width=(IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha).width:=rfl

theorem target_source_degree (root :List Bool) (i :ℕ) :
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).degree
      (pair root (BinaryNatCode.encode i))≤2^(P).width root:=by
  rw [target_width hn ht ha hR0]
  exact IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha (radius R0) root i

theorem prelude_commands (root :List Bool) :
    IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root 0 (Nat.zero_le _)=
    IntegralMixedSourceIntegerPrelude.commands P (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0))
      (fun r=>IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)) (fun r=>number n r+8)
      (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha (radius R0))
      (target_source_degree hn ht ha hR0) root:=by
  unfold IntegralMixedMarkedRecordContinuation.oldCommands
  simp only [initial_records]
  unfold IntegralMixedStaticRecordPrefix.originals
  have HC :number n root+8≤(P).cap root+1+1:=
    (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)
  have HE:=integer_commands (initial P D root) (Q root)
    (IntegralMixedStaticRecordPrefix.cap (Q root) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root))
    (number n root+8)
    (fun i=>IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root (number n root+8-1-i.val))
    (fun i=>IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root _)
    (fun i=>IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root _) HC
  refine HE.trans ?_
  unfold IntegralMixedSourceIntegerPrelude.commands
  apply congrArg List.ofFn
  funext i
  rfl

private theorem realizes_commands {a S B :ℕ} {V :SpatialSource a}
    (initial :State V S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) (v :ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes (run initial cs hc) v→
      IntegralMixedIntegerRealization.Realizes (run initial ds hd) v:=by
  cases he
  exact id

private theorem realizes_reframe {a b S B m :ℕ} {V :SpatialSource a} {ι :Type}
    (x :State V S B m ι) (W :SpatialSource b)
    (hc :PurePowerReductionBounds.dimension (b+1) W.degree≤2^B) (v :ℕ→ℝ)
    (H :IntegralMixedIntegerRealization.Realizes x v) :
    IntegralMixedIntegerRealization.Realizes (reframe x W hc) v:=H

noncomputable def preludeState (root :List Bool):=
  reframe (run (initial P D root)
    (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root 0 (Nat.zero_le _))
    (by rw [IntegralMixedMarkedRecordContinuation.oldCommands_length];
        exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)))
    (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root))

noncomputable def prescribed (root :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate root))
    (q :MvPolynomial (Fin (number n root)) ℤ) (a :BoundedZeroSource.Bounded q (radius R0 root)) :ℕ→ℝ:=
  fun j=>IntegralMixedAuxiliaryMarkedIntegerSource.values n t (radius R0) root
    (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha root hq)
    (BoundedRegularSource.sphereSlack q (radius R0 root) a)
    (BoundedRegularSource.regularSlack q
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original root))
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original root)) (radius R0 root) a).re
    (number n root+8-1-j)

theorem prelude_realizes (root :List Bool)
    (hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate root))
    (q :MvPolynomial (Fin (number n root)) ℤ) (a :BoundedZeroSource.Bounded q (radius R0 root))
    (ha0 :∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha
      (IntegralMixedAuxiliaryMarkedIntegerSource.candidate root) hq i) :
    IntegralMixedIntegerRealization.Realizes (preludeState hn ht ha hR0 root)
      (prescribed hn ht ha (R0:=R0) root hq q a):=by
  have HS:=IntegralMixedAuxiliaryMarkedSlackRoots.roots hn ht ha (radius R0) root hq q a ha0
  let v:=IntegralMixedAuxiliaryMarkedIntegerSource.values n t (radius R0) root
    (IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues hn ht ha root hq)
    (BoundedRegularSource.sphereSlack q (radius R0 root) a)
    (BoundedRegularSource.regularSlack q
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original root))
      (AuxiliaryCandidateRegularLift.allowance t (IntegralMixedAuxiliaryMarkedIntegerSource.original root)) (radius R0 root) a).re
  have HR:=IntegralMixedSourceIntegerPrelude.realizes P
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0))
    (fun r=>IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)) (fun r=>number n r+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha (radius R0)) (target_source_degree hn ht ha hR0)
    root (initial P D root) (fun i:Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i)
    (by rw [IntegralMixedSourceIntegerPrelude.commands_length];
        exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)) v
    (fun i _=>IntegralMixedAuxiliaryMarkedIntegerSource.roots hn ht ha (radius R0) root _ _ _
      (IntegralMixedAuxiliaryMarkedCandidateRealization.coordinate_root hn ht ha root hq) HS.1 HS.2 i)
  have HRoom :number n root+8≤(P).cap root+1+1:=
    (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)
  have HE:=realizes_commands (initial P D root) _ _
    (by rw [IntegralMixedSourceIntegerPrelude.commands_length];exact HRoom)
    (by rw [IntegralMixedMarkedRecordContinuation.oldCommands_length];simpa only [Nat.add_zero] using HRoom)
    (prelude_commands hn ht ha hR0 root).symm (prescribed hn ht ha (R0:=R0) root hq q a) HR
  unfold preludeState
  exact realizes_reframe _ _ _ _ HE

private theorem root_context (u label :List Bool) :root hn ht ha hR0 u label=
    IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label
      (pair (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload (n u+3))) []):=by
  unfold root IntegralMixedRoadmapSeedResampling.preparedRoot
  rw [packet_eq hn ht ha hR0 u label []]
  simp only [IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapAtomic.packet,IntegralMixedRoadmapAtomic.candidate,
    IntegralMixedRoadmapAtomic.payload,pairFst_pair,pairSnd_pair,IntegralMixedAuxiliaryMarkedCandidateAtRadius.context]

noncomputable def BoundedWitness (ctx :List Bool) :Prop:=
  ∃hq :IntegralMixedAuxiliaryCandidate.Valid hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate ctx),
  ∃a :BoundedZeroSource.Bounded (IntegralMixedAuxiliaryMarkedCandidateAtRadius.polynomial n t ctx) (radius R0 ctx),
    ∀i,a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha (IntegralMixedAuxiliaryMarkedIntegerSource.candidate ctx) hq i

theorem bounded_witness (u label :List Bool)
    (hg :LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hLower :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u) :
    BoundedWitness hn ht ha (R0:=R0) (root hn ht ha hR0 u label):=by
  let outer:=pair (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload (n u+3))) []
  let ctx:=IntegralMixedAuxiliaryMarkedCandidateAtRadius.context u label outer
  have HR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤radius R0 ctx:=by
    simpa only [ctx,IntegralMixedAuxiliaryMarkedCandidateAtRadius.context,radius,
      IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair] using hLower
  have HW :BoundedWitness hn ht ha (R0:=R0) ctx:=
    ⟨IntegralMixedAuxiliaryMarkedCandidateAtRadius.valid hn ht ha u label outer hg,
      IntegralMixedAuxiliaryMarkedCandidateAtRadius.boundedPoint hn ht ha (radius R0) u label outer hg HR,
      IntegralMixedAuxiliaryMarkedCandidateAtRadius.coordinate hn ht ha (radius R0) u label outer hg HR⟩
  exact Eq.mpr (congrArg (BoundedWitness hn ht ha (R0:=R0)) (root_context hn ht ha hR0 u label)) HW

end LeanCanny.Encoding.IntegralMixedRoadmapFirstSeed
