/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedCertifiedReplay

/-! # One native complete marked vertex realizes every prescribed bank value -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedNativeVertex
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedAuxiliaryMarkedIntegerPlan (parameters plan certifiedParameters certifiedPlan certifiedData bankKey bank)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context replayState replayValues native_radius_le)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev input {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) := IntegralFramedBankQuery.input (bank hn ht ha hR)

theorem input_access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : (input hn ht ha hR).Access :=
  IntegralFramedBankQuery.input_access _ (IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR)

theorem input_complete {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : SquareSampleComplete.Complete (input hn ht ha hR) :=
  IntegralFramedCompleteSquare.complete (bank hn ht ha hR).parameters (bank hn ht ha hR).plan (bank hn ht ha hR).data
    (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed (bank hn ht ha hR).bounds
    (bank hn ht ha hR).key (bank hn ht ha hR).positive

theorem count {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx : List Bool) :
    (input hn ht ha hR).count (sampleContext ctx)=((plan hn ht ha R).rules ctx).length := by
  change (IntegralMixedFramedBankSnapshotBits.atKey (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR)
    (certifiedData hn ht ha hR) (bankKey n (sampleContext ctx))).count=_
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.bank_count,IntegralMixedAuxiliaryMarkedCertifiedReplay.rules_length]
  simp only [sampleContext,pairFst_pair]

theorem rows {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx : List Bool) :
    HEq ((input hn ht ha hR).system (sampleContext ctx)) (replayState hn ht ha R ctx).sampler.scalarPrefix.rows :=
  (IntegralFramedCompleteSquare.rows_heq (bank hn ht ha hR).parameters (bank hn ht ha hR).plan (bank hn ht ha hR).data
    (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed (bank hn ht ha hR).bounds
    (bank hn ht ha hR).key (bank hn ht ha hR).positive (sampleContext ctx)).trans
    (IntegralMixedAuxiliaryMarkedCertifiedReplay.rows_at_key hn ht ha hR ctx)

noncomputable def observation {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx : List Bool) :=
  IntegralMixedFramedBankObservation.ofState ((IntegralMixedFramedHistoryFamilyBits.family
    (certifiedParameters hn ht ha hR) (certifiedPlan hn ht ha hR) (certifiedData hn ht ha hR)).state (bankKey n (sampleContext ctx)))

attribute [local irreducible] parameters

theorem exists_for_radius {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    let ctx:=context u label outer
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
      w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext ctx) ∧ ∀i<number n ctx+8,
        (observation hn ht ha hR ctx).point
          (IntegralMixedFramedBankObservation.extend
            (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hw).val) i=
          replayValues hn ht ha R u label outer hg
            hLower i := by
  let ctx:=context u label outer
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralMixedRealizedCompleteVertex.exists_observed
    (replayState hn ht ha _ ctx) (IntegralMixedAuxiliaryMarkedCandidateVertex.canonical hn ht ha _ ctx)
    (IntegralMixedAuxiliaryMarkedCandidateVertex.scalarOnly hn ht ha _ ctx)
    (input hn ht ha hR) (input_complete hn ht ha hR) (sampleContext ctx) (count hn ht ha hR ctx) (rows hn ht ha hR ctx) _
    (IntegralMixedAuxiliaryMarkedCandidateAtRadius.realizes hn ht ha R u label outer hg hLower)
  refine ⟨w,hw,hlen,fun i hi=>?_⟩
  have HI : i<((plan hn ht ha R).rules ctx).length := by
    rw [IntegralMixedAuxiliaryMarkedCertifiedReplay.rules_length]
    exact hi
  exact (congrArg (fun d : IntegralMixedFramedBankObservation.Data=>d.point
    (IntegralMixedFramedBankObservation.extend
      (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hw).val) i)
      (IntegralMixedAuxiliaryMarkedCertifiedReplay.data_at_key hn ht ha hR ctx)).trans (hvalues i HI)


theorem exists_vertex {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) (hg : Good hn ht ha u label) :
    let hR:=IntegralMixedAuxiliaryMarkedIntegerPlan.radius_binary hn ht ha
    let ctx:=context u label outer
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
      w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext ctx) ∧ ∀i<number n ctx+8,
        (observation hn ht ha hR ctx).point
          (IntegralMixedFramedBankObservation.extend
            (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hw).val) i=
          replayValues hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius hn ht ha) u label outer hg
            (native_radius_le hn ht ha u label outer) i :=
  exists_for_radius hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius_binary hn ht ha) u label outer hg
    (native_radius_le hn ht ha u label outer)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedNativeVertex
