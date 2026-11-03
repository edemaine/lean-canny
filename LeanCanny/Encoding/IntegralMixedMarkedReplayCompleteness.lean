/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedCanonicalValues

/-! # One native vertex satisfies marked membership and the old-point comparison -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReplayCompleteness
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedAuxiliaryMarkedCandidateAtRadius (context valid polynomial boundedPoint replayValues)
open IntegralMixedAuxiliaryMarkedNativeVertex (input observation)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open IntegralMixedMarkedCanonicalValues (chronological)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.parameters
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryCandidate.vertex IntegralMixedAuxiliaryCandidate.input
  IntegralMixedAuxiliaryCandidate.point IntegralMixedAuxiliaryCandidate.joint
  IntegralMixedAuxiliaryParameters.parameters IntegralMixedAuxiliaryRecipeRoot.planAt IntegralMixedAuxiliaryRecipeRoot.dataAt

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (u label outer : List Bool) (hg : Good hn ht ha u label)
  (hLower : IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R (context u label outer))
  (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext (context u label outer)) w)
  (H : ∀j<number n (context u label outer)+8,
    (observation hn ht ha hR (context u label outer)).point
      (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate
        (input hn ht ha hR) (sampleContext (context u label outer)) w hw).val) j=
      replayValues hn ht ha R u label outer hg hLower j)

include H in
theorem leaf_value (i : ℕ) (hi : i<number n (context u label outer)+8) :
    IntegralMixedMarkedLeafTest.point hn ht ha hR (context u label outer) w hw i=
      chronological hn ht ha R u label outer hg hLower i :=
  (H _ (by omega)).trans (IntegralMixedMarkedCanonicalValues.reverse_value hn ht ha R u label outer hg hLower i hi)

include H in
theorem point_values :
    IntegralMixedMarkedPointReadback.point hn ht ha hR (context u label outer) w hw=
      (fun i : Fin (number n (context u label outer)+4)=>chronological hn ht ha R u label outer hg hLower i.val) := by
  funext i
  exact (IntegralMixedMarkedPointReadback.coordinate hn ht ha hR (context u label outer) w hw i.val (by omega)).trans
    (leaf_value hn ht ha hR u label outer hg hLower w hw H i.val (by omega))

include H in
theorem accepted_marked :
    pair (context u label outer) w∈IntegralMixedMarkedPointTest.language hn ht ha hR := by
  apply (IntegralMixedMarkedReplayValidity.accepted_iff hn ht ha hR (context u label outer) w).mpr
  refine ⟨hw,?_,?_⟩
  · intro i hi
    rw [leaf_value hn ht ha hR u label outer hg hLower w hw H i hi]
    exact IntegralMixedMarkedCanonicalValues.roots hn ht ha R u label outer hg hLower i
  · refine ⟨BoundedRegularSource.markedLift (polynomial n t (context u label outer))
      (AuxiliaryCandidateRegularLift.allowance t (original (context u label outer)))
      (AuxiliaryCandidateRegularLift.allowance t (original (context u label outer))) (R (context u label outer))
      (boundedPoint hn ht ha R u label outer hg hLower),?_⟩
    exact (IntegralMixedMarkedCanonicalValues.marked_coordinates hn ht ha R u label outer hg hLower).symm.trans
      (point_values hn ht ha hR u label outer hg hLower w hw H).symm

include H in
theorem accepted_thom :
    pair (context u label outer) w∈IntegralMixedCandidateReplayThom.language hn ht ha hR := by
  apply (IntegralMixedAuxiliaryMarkedThomCompleteness.packet_iff hn ht ha hR _ w).mpr
  refine ⟨valid hn ht ha u label outer hg,hw,fun i=>?_⟩
  rw [IntegralMixedAuxiliaryMarkedThomCompleteness.point_eq_observed]
  exact ((H _ (by omega)).trans
    (IntegralMixedAuxiliaryMarkedOriginalReadback.replay_original hn ht ha R u label outer hg hLower i)).symm

omit w hw H in
include hg hLower in
theorem exists_accepted :
    ∃w : List Bool,w.length=SquareSampleCompleteVertices.width (input hn ht ha hR) (sampleContext (context u label outer)) ∧
      pair (context u label outer) w∈IntegralMixedCandidateReplayThom.language hn ht ha hR ∧
      pair (context u label outer) w∈IntegralMixedMarkedPointTest.language hn ht ha hR := by
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralMixedAuxiliaryMarkedNativeVertex.exists_for_radius hn ht ha hR u label outer hg hLower
  exact ⟨w,hlen,accepted_thom hn ht ha hR u label outer hg hLower w hw hvalues,
    accepted_marked hn ht ha hR u label outer hg hLower w hw hvalues⟩

end LeanCanny.Encoding.IntegralMixedMarkedReplayCompleteness
