/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCandidateGoodTest

/-! # Every accepted phase attaches to the same original candidate

Accepted replay words may choose different real slack phases. Their actual
marked points belong to one connected component of the full regular zero set.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReplayAttachment
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate original)
open IntegralMixedAuxiliaryMarkedNativeVertex (input)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open IntegralMixedMarkedPointTest (charge)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.parameters
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.input
  IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

theorem exists_point (ctx w : List Bool)
    (h : pair ctx w∈IntegralMixedMarkedReplayRelation.language hn ht ha hR) :
    ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (candidate ctx),
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w,
    ∃z : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (charge t ctx) (charge t ctx) (R ctx),
      z.val.val=IntegralMixedMarkedPointReadback.point hn ht ha hR ctx w hv ∧
      (BoundedRegularSource.markedProjection _ _ _ _ z).val=
        IntegralMixedAuxiliaryCandidate.point hn ht ha (candidate ctx) hp := by
  obtain ⟨hp,_,HE⟩:=(IntegralMixedAuxiliaryMarkedThomCompleteness.packet_iff hn ht ha hR ctx w).mp h.1
  obtain ⟨hv,_,z,hz⟩:=(IntegralMixedMarkedReplayValidity.accepted_iff hn ht ha hR ctx w).mp h.2
  exact ⟨hp,hv,z,hz,IntegralMixedMarkedReplayRelation.projection_eq hn ht ha hR ctx w hp hv z hz HE⟩

theorem accepted_points_joined (ctx w v : List Bool)
    (hw : pair ctx w∈IntegralMixedMarkedReplayRelation.language hn ht ha hR)
    (hv : pair ctx v∈IntegralMixedMarkedReplayRelation.language hn ht ha hR)
    (hzw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (hzv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) v)
    (z y : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (charge t ctx) (charge t ctx) (R ctx))
    (hz : z.val.val=IntegralMixedMarkedPointReadback.point hn ht ha hR ctx w hzw)
    (hy : y.val.val=IntegralMixedMarkedPointReadback.point hn ht ha hR ctx v hzv) :
    Joined z.val y.val := by
  obtain ⟨hp,_,HE⟩:=(IntegralMixedAuxiliaryMarkedThomCompleteness.packet_iff hn ht ha hR ctx w).mp hw.1
  obtain ⟨hp',_,HE'⟩:=(IntegralMixedAuxiliaryMarkedThomCompleteness.packet_iff hn ht ha hR ctx v).mp hv.1
  have HZ:=IntegralMixedMarkedReplayRelation.projection_eq hn ht ha hR ctx w hp hzw z hz HE
  have HY:=IntegralMixedMarkedReplayRelation.projection_eq hn ht ha hR ctx v hp' hzv y hy HE'
  have HP : BoundedRegularSource.markedProjection _ _ _ _ z=
      BoundedRegularSource.markedProjection _ _ _ _ y := Subtype.ext (HZ.trans HY.symm)
  have JZ:=BoundedRegularSource.joined_to_lift _ _ _ _ z
  have JY:=BoundedRegularSource.joined_to_lift _ _ _ _ y
  rw [HP] at JZ
  exact JZ.trans JY.symm

end LeanCanny.Encoding.IntegralMixedMarkedReplayAttachment
