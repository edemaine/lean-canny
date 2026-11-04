/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorOriginalPoints
/-! # Actual marked paths and bounded original components in one input domain -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

private theorem integer_component_joined {a :ℕ} (Q :MvPolynomial (Fin a) ℤ)
    (x y :Fin a→ℝ) (hx :Q.eval₂ (Int.castRingHom ℝ) x=0)
    (hy :y∈connectedComponentIn {v |Q.eval₂ (Int.castRingHom ℝ) v=0} x):
    JoinedIn {v |Q.eval₂ (Int.castRingHom ℝ) v=0} x y:=by
  simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using
    PolynomialComponentPaths.joinedIn_of_component (Q.map (Int.castRingHom ℝ)) x
      (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,Set.mem_ofPred_eq] using hx) y
      (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using hy)

theorem source_joined_of_component (u :List Bool) (x y :Fin (n u+4)→ℝ)
    (hx :x∈IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
    (hy :y∈connectedComponentIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u) x):
    JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u) x y:=
  integer_component_joined _ x y hx hy

theorem marked_joined_iff (u :List Bool)
    (z v :BoundedRegularSource.Marked ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u)):
    JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u) z.val.val v.val.val ↔
      (BoundedRegularSource.markedProjection _ _ _ _ v).val∈
        connectedComponentIn (BoundedZeroSource.Bounded ((t u).finitePolynomial (n u)) (R0 u))
          (BoundedRegularSource.markedProjection _ _ _ _ z).val:=by
  have HM:=BoundedRegularSource.marked_component_iff ((t u).finitePolynomial (n u))
    (t u).toData.size (t u).toData.size (R0 u)
    (AuxiliaryCandidateRegularLift.original_degree n t u) (AuxiliaryCandidateRegularLift.original_mass n t u) z v
  unfold IntegralMixedRoadmapGraph.firstZeroSet
  rw [IntegralMixedOriginalRegularSource.source_polynomial]
  constructor
  · intro H
    have HJ:Joined z.val v.val:=(joinedIn_iff_joined z.val.property v.val.property).mp H
    exact HM.mp (pathComponent_subset_component z.val HJ)
  · intro H
    have HC:=HM.mpr H
    have HA:v.val.val∈connectedComponentIn
        {p |(BoundedRegularSource.polynomial ((t u).finitePolynomial (n u))
          (t u).toData.size (t u).toData.size (R0 u)).eval₂ (Int.castRingHom ℝ) p=0} z.val.val:=by
      change v.val.val∈connectedComponentIn (BoundedRegularSource.Zeros ((t u).finitePolynomial (n u))
        (t u).toData.size (t u).toData.size (R0 u)) z.val.val
      rw [connectedComponentIn_eq_image z.val.property]
      exact ⟨v.val,HC,rfl⟩
    exact integer_component_joined _ _ _ z.val.property HA

theorem prelude_joined_first_marked (u label q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=pair u label)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label)
    (hR :IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha u≤R0 u):
    JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
      (prelude hn ht ha hR0 u q hv) (IntegralMixedRoadmapGraph.firstMarkedPoint hn ht ha u label hg hR):=by
  obtain ⟨z,HZ,HP⟩:=prelude_marked hn ht ha hR0 u label q hv hc hr hg
  let a:=AuxiliaryCandidateOuterRadius.boundedPoint hn ht ha u label hg (R0 u) hR
  have HProj:BoundedRegularSource.markedProjection _ _ _ _ z=a:=by
    apply Subtype.ext
    funext i
    exact (congrFun HP i).trans (AuxiliaryCandidateOuterRadius.coordinate hn ht ha u label hg (R0 u) hR i).symm
  have HJ:=BoundedRegularSource.joined_to_lift _ _ _ _ z
  rw [HProj] at HJ
  have H:JoinedIn
      {p |(BoundedRegularSource.polynomial ((t u).finitePolynomial (n u))
        (t u).toData.size (t u).toData.size (R0 u)).eval₂ (Int.castRingHom ℝ) p=0}
      z.val.val (IntegralMixedRoadmapGraph.firstMarkedPoint hn ht ha u label hg hR):=
    (joinedIn_iff_joined z.val.property
      (BoundedRegularSource.lift _ _ _ _ a).property).mpr HJ
  rw [HZ] at H
  simpa only [IntegralMixedRoadmapGraph.firstZeroSet,IntegralMixedOriginalRegularSource.source_polynomial] using H

end LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
