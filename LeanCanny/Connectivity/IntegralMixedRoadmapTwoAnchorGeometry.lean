/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorCost
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorReplaySeed
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorMarkedPaths
/-! # Two native anchors recognize bounded original component membership

Both candidate points are genuine zeros and the radius is fixed before either
word is sampled. The same actual critical point initializes two independent
Replay words in the completeness direction.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedAuxiliaryCandidate.pointAt
  AuxiliaryCandidateOuterRadius.boundedPoint IntegralMixedRoadmapGraph.firstMarkedPoint point prelude

theorem component_of_language (u a b :List Bool)
    (hA :AuxiliaryCandidateComponentCover.Good hn ht ha u a)
    (hB :AuxiliaryCandidateComponentCover.Good hn ht ha u b)
    (H :pair u (pair a b)∈IntegralMixedRoadmapTwoAnchorCost.language hn ht ha hR0):
    IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u b (Classical.choose hB)∈
      connectedComponentIn (BoundedZeroSource.Bounded ((t u).finitePolynomial (n u)) (R0 u))
        (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u a (Classical.choose hA)):=by
  obtain ⟨sa,sb,hva,hvb,hda,hra,hia,hdb,hrb,hib,HE⟩:=
    (IntegralMixedRoadmapTwoAnchorCost.language_iff_points hn ht ha hR0 _).mp H
  have HA:IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (pair u a) sa:=by
    simpa only [IntegralMixedRoadmapTwoAnchorCost.candidate,pairFst_pair,pairSnd_pair,
      Bool.false_eq_true,ite_false] using hia
  have HB:IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (pair u b) sb:=by
    simpa only [IntegralMixedRoadmapTwoAnchorCost.candidate,pairFst_pair,pairSnd_pair,ite_true] using hib
  have hca:IntegralMixedRoadmapAtomic.candidate sa=pair u a:=by
    obtain ⟨_,_,HR⟩:=HA
    exact HR.2.2.1
  have hcb:IntegralMixedRoadmapAtomic.candidate sb=pair u b:=by
    obtain ⟨_,_,HR⟩:=HB
    exact HR.2.2.1
  have HP:point hn ht ha hR0 u a sa hva hca=point hn ht ha hR0 u b sb hvb hcb:=
    eq_of_heq ((point_heq hn ht ha hR0 u a sa hva hca).symm.trans
      (HE.trans (point_heq hn ht ha hR0 u b sb hvb hcb)))
  have JA:=(incidence_iff_joined hn ht ha hR0 u a sa hva hca hda hra).mp HA
  have JB:=(incidence_iff_joined hn ht ha hR0 u b sb hvb hcb hdb hrb).mp HB
  rw [HP] at JA
  have J:=JA.symm.trans JB
  obtain ⟨z,HZ,HZA⟩:=prelude_marked hn ht ha hR0 u a sa hva hca hra hA
  obtain ⟨v,HV,HVB⟩:=prelude_marked hn ht ha hR0 u b sb hvb hcb hrb hB
  rw [←HZ,←HV] at J
  have HC:=(marked_joined_iff (n:=n) (t:=t) (R0:=R0) u z v).mp J
  simpa only [HZA,HVB] using HC

theorem language_iff_component (u a b :List Bool)
    (hA :AuxiliaryCandidateComponentCover.Good hn ht ha u a)
    (hB :AuxiliaryCandidateComponentCover.Good hn ht ha u b)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u):
    pair u (pair a b)∈IntegralMixedRoadmapTwoAnchorCost.language hn ht ha hR0 ↔
      IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u b (Classical.choose hB)∈
        connectedComponentIn (BoundedZeroSource.Bounded ((t u).finitePolynomial (n u)) (R0 u))
          (IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u a (Classical.choose hA)):=by
  constructor
  · exact component_of_language hn ht ha hR0 u a b hA hB
  · intro H
    let z:=BoundedRegularSource.markedLift ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u)
      (AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u a hA (R0 u) hR)
    let v:=BoundedRegularSource.markedLift ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u)
      (AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u b hB (R0 u) hR)
    have JAB:JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
        (IntegralMixedRoadmapGraph.firstMarkedPoint hn ht ha u a hA hR)
        (IntegralMixedRoadmapGraph.firstMarkedPoint hn ht ha u b hB hR):=by
      have HZa:(AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u a hA (R0 u) hR).val=
          IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u a (Classical.choose hA):=
        funext fun i=>AuxiliaryCandidateOuterRadius.coordinate hn ht ha u a hA (R0 u) hR i
      have HVb:(AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u b hB (R0 u) hR).val=
          IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u b (Classical.choose hB):=
        funext fun i=>AuxiliaryCandidateOuterRadius.coordinate hn ht ha u b hB (R0 u) hR i
      unfold IntegralMixedRoadmapGraph.firstMarkedPoint
      apply (marked_joined_iff (n:=n) (t:=t) (R0:=R0) u z v).mpr
      simpa only [z,v,BoundedRegularSource.markedProjection_lift,HZa,HVb] using H
    obtain ⟨p,HP,HZ,HG⟩:=IntegralMixedRoadmapGraph.exists_original_component_critical hn ht ha u a hA hR
    have JAp:=source_joined_of_component (n:=n) (t:=t) (R0:=R0) u
      (IntegralMixedRoadmapGraph.firstMarkedPoint hn ht ha u a hA hR) p
      (IntegralMixedRoadmapGraph.firstMarkedPoint_mem hn ht ha u a hA hR) HP
    obtain ⟨sa,hva,hca,hda,hra,HPA⟩:=exists_replay_at_original hn ht ha hR0 u a hA hR p HZ HG
    obtain ⟨sb,hvb,hcb,hdb,hrb,HPB⟩:=exists_replay_at_original hn ht ha hR0 u b hB hR p HZ HG
    have HA:IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (pair u a) sa:=by
      apply (incidence_iff_joined hn ht ha hR0 u a sa hva hca hda hra).mpr
      rw [HPA]
      exact JAp.symm.trans (prelude_joined_first_marked hn ht ha hR0 u a sa hva hca hra hA hR).symm
    have HB:IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (pair u b) sb:=by
      apply (incidence_iff_joined hn ht ha hR0 u b sb hvb hcb hdb hrb).mpr
      rw [HPB]
      exact (JAp.symm.trans JAB).trans (prelude_joined_first_marked hn ht ha hR0 u b sb hvb hcb hrb hB hR).symm
    have HE:HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 sa hva)
        (IntegralMixedRoadmapIdentity.point hn ht ha hR0 sb hvb):=
      (point_heq hn ht ha hR0 u a sa hva hca).trans
        ((heq_of_eq (HPA.trans HPB.symm)).trans (point_heq hn ht ha hR0 u b sb hvb hcb).symm)
    apply (IntegralMixedRoadmapTwoAnchorCost.language_iff_points hn ht ha hR0 _).mpr
    refine ⟨sa,sb,hva,hvb,hda,hra,?_,hdb,hrb,?_,HE⟩
    · simpa only [IntegralMixedRoadmapTwoAnchorCost.candidate,pairFst_pair,pairSnd_pair,
        Bool.false_eq_true,ite_false] using HA
    · simpa only [IntegralMixedRoadmapTwoAnchorCost.candidate,pairFst_pair,pairSnd_pair,ite_true] using HB

end LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
