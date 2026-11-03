/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOriginalReadback
public import LeanCanny.Encoding.IntegralMixedCandidateReplayThom

/-! # Filtered old candidates have native replays accepted by the Thom decider -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedThomCompleteness
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context valid)
open IntegralMixedAuxiliaryMarkedNativeVertex (input observation)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem fields_iff {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (q ctx w : List Bool)
    (hc : IntegralMixedCandidateReplayThom.context q=ctx) (hw : IntegralMixedCandidateReplayThom.word q=w) :
    q∈IntegralMixedCandidateReplayThom.language hn ht ha hR ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx),
      ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
        ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp i=
          IntegralMixedCandidateReplayNew.point hn ht ha hR ctx w hv i := by
  cases hc
  cases hw
  exact IntegralMixedCandidateReplayThom.language_iff hn ht ha hR q

theorem packet_iff {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx w : List Bool) :
    pair ctx w∈IntegralMixedCandidateReplayThom.language hn ht ha hR ↔
      ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx),
      ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
        ∀i : Fin (number n ctx),IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp i=
          IntegralMixedCandidateReplayNew.point hn ht ha hR ctx w hv i :=
  fields_iff hn ht ha hR (pair ctx w) ctx w (pairFst_pair ctx w) (pairSnd_pair ctx w)

theorem point_eq_observed {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) (i : Fin (number n ctx)) :
    IntegralMixedCandidateReplayNew.point hn ht ha hR ctx w hv i=(observation hn ht ha hR ctx).point
      (IntegralMixedFramedBankObservation.extend
        (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hv).val) (number n ctx+7-i.val) := rfl

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliaryMarkedIntegerPlan.parameters

theorem exists_accepted {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    ∃w : List Bool,w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext (context u label outer)) ∧
      pair (context u label outer) w∈IntegralMixedCandidateReplayThom.language hn ht ha hR := by
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralMixedAuxiliaryMarkedOriginalReadback.exists_for_radius hn ht ha hR u label outer hg hLower
  refine ⟨w,hlen,(packet_iff hn ht ha hR _ w).mpr ⟨valid hn ht ha u label outer hg,hw,fun i=>?_⟩⟩
  rw [point_eq_observed]
  exact (hvalues i).symm

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedThomCompleteness
