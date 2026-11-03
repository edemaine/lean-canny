/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalReplayRelation

/-! # Every accepted phase attaches to the same original candidate

Accepted full physical replay words may choose different real slack phases. Their actual
marked points belong to one connected component of the full regular zero set.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalReplayAttachment
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralMixedMarkedPointTest (charge)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.parameters
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.input
  IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem exists_point (ctx w : List Bool)
    (h : pair ctx w∈IntegralMixedPhysicalReplayRelation.language hn ht ha hR outer) :
    ∃hp : IntegralMixedAuxiliaryCandidate.Valid hn ht ha (pairFst ctx),
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
    ∃z : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (charge t ctx) (charge t ctx) (R ctx),
      z.val.val=IntegralMixedPhysicalMarkedSemantics.point hn ht ha hR outer ctx w hv ∧
      (BoundedRegularSource.markedProjection _ _ _ _ z).val=
        IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx) hp := by
  obtain ⟨hp,_,HE⟩:=(IntegralMixedPhysicalReplayRelation.thom_packet hn ht ha hR outer ctx w).mp h.1
  obtain ⟨hv,_,z,hz⟩:=(IntegralMixedPhysicalMarkedValidity.accepted_iff hn ht ha hR outer ctx w).mp h.2
  exact ⟨hp,hv,z,hz,IntegralMixedPhysicalReplayRelation.projection_eq hn ht ha hR outer ctx w hp hv z hz HE⟩

theorem accepted_points_joined (ctx w v : List Bool)
    (hw : pair ctx w∈IntegralMixedPhysicalReplayRelation.language hn ht ha hR outer)
    (hv : pair ctx v∈IntegralMixedPhysicalReplayRelation.language hn ht ha hR outer)
    (hzw : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (hzv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) v)
    (z y : BoundedRegularSource.Marked ((t (original ctx)).finitePolynomial (number n ctx))
      (charge t ctx) (charge t ctx) (R ctx))
    (hz : z.val.val=IntegralMixedPhysicalMarkedSemantics.point hn ht ha hR outer ctx w hzw)
    (hy : y.val.val=IntegralMixedPhysicalMarkedSemantics.point hn ht ha hR outer ctx v hzv) :
    Joined z.val y.val := by
  obtain ⟨hp,_,HE⟩:=(IntegralMixedPhysicalReplayRelation.thom_packet hn ht ha hR outer ctx w).mp hw.1
  obtain ⟨hp',_,HE'⟩:=(IntegralMixedPhysicalReplayRelation.thom_packet hn ht ha hR outer ctx v).mp hv.1
  have HZ:=IntegralMixedPhysicalReplayRelation.projection_eq hn ht ha hR outer ctx w hp hzw z hz HE
  have HY:=IntegralMixedPhysicalReplayRelation.projection_eq hn ht ha hR outer ctx v hp' hzv y hy HE'
  have HP : BoundedRegularSource.markedProjection _ _ _ _ z=
      BoundedRegularSource.markedProjection _ _ _ _ y := Subtype.ext (HZ.trans HY.symm)
  have JZ:=BoundedRegularSource.joined_to_lift _ _ _ _ z
  have JY:=BoundedRegularSource.joined_to_lift _ _ _ _ y
  rw [HP] at JZ
  exact JZ.trans JY.symm

end LeanCanny.Encoding.IntegralMixedPhysicalReplayAttachment
