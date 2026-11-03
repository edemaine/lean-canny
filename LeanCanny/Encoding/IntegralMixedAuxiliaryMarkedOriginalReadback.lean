/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedNativeVertex

/-! # The one native replay vertex retains the literal old original point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOriginalReadback
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context replayValues valid native_radius_le)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open IntegralMixedAuxiliaryMarkedNativeVertex (input observation)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem replay_original {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hR : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer))
    (i : Fin (number n (context u label outer))) :
    replayValues hn ht ha R u label outer hg hR (number n (context u label outer)+7-i.val)=
      IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate (context u label outer))
        (valid hn ht ha u label outer hg) i := by
  have HJ : number n (context u label outer)+8-1-(number n (context u label outer)+7-i.val)=i.val := by omega
  simp only [replayValues,IntegralMixedAuxiliaryMarkedIntegerSource.values,HJ,ite_eq_left i.isLt,
    IntegralMixedAuxiliaryMarkedCandidateRealization.oldValues,dite_eq_left i.isLt]
  rfl

attribute [local irreducible] IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex
  IntegralMixedAuxiliaryCandidate.input IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt
  IntegralMixedAuxiliaryMarkedIntegerPlan.parameters

theorem exists_for_radius {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) (u label outer : List Bool) (hg : Good hn ht ha u label)
    (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer)) :
    let ctx:=context u label outer
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
      w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext ctx) ∧ ∀i : Fin (number n ctx),
        (observation hn ht ha hR ctx).point
          (IntegralMixedFramedBankObservation.extend
            (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hw).val)
              (number n ctx+7-i.val)=
          IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) (valid hn ht ha u label outer hg) i := by
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralMixedAuxiliaryMarkedNativeVertex.exists_for_radius hn ht ha hR u label outer hg hLower
  exact ⟨w,hw,hlen,fun i=>(hvalues _ (by omega)).trans
    (replay_original hn ht ha _ u label outer hg hLower i)⟩


theorem exists_vertex {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (u label outer : List Bool) (hg : Good hn ht ha u label) :
    let hR:=IntegralMixedAuxiliaryMarkedIntegerPlan.radius_binary hn ht ha
    let ctx:=context u label outer
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
      w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext ctx) ∧ ∀i : Fin (number n ctx),
        (observation hn ht ha hR ctx).point
          (IntegralMixedFramedBankObservation.extend
            (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hw).val)
              (number n ctx+7-i.val)=
          IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) (valid hn ht ha u label outer hg) i :=
  exists_for_radius hn ht ha (IntegralMixedAuxiliaryMarkedIntegerPlan.radius_binary hn ht ha) u label outer hg
    (native_radius_le hn ht ha u label outer)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOriginalReadback
