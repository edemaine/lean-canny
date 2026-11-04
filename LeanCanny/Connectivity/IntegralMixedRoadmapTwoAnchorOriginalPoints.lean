/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidenceGeometry
public import LeanCanny.Connectivity.IntegralMixedRoadmapFirstSeedComponent
public import LeanCanny.Geometry.PolynomialComponentPaths
/-! # Put the two independently sampled anchors in one original spatial domain -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_point_heq {a b :ℕ} (H :a=b) (p :Fin a→ℝ):
    HEq p (fun i :Fin b=>p (Fin.cast H.symm i)):=by cases H;rfl
private theorem restriction_heq {a b :ℕ} (H :a=b) (v :ℕ→ℝ):
    HEq (fun i :Fin a=>v i.val) (fun i :Fin b=>v i.val):=by cases H;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapGraph.pointAt IntegralMixedRoadmapGraph.preludeAt
  IntegralMixedRoadmapIdentity.point IntegralMixedRoadmapMarkedPrelude.value

noncomputable def point (u label q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=pair u label):Fin (n u+4)→ℝ:=fun i=>
  IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 (pair u label) q hv hc
    (Fin.cast (congrArg (fun v :List Bool=>n v+4) (pairFst_pair u label)).symm i)
noncomputable def prelude (u q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q):
    Fin (n u+4)→ℝ:=fun i=>IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 q hv i.val

theorem point_heq (u label q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=pair u label):
    HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv) (point hn ht ha hR0 u label q hv hc):=by
  have HA:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapIdentity.point
    exact cast_point_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)) _
  have HB:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 (pair u label) q hv hc):=by
    unfold IntegralMixedRoadmapGraph.pointAt
    exact cast_point_heq (congrArg (·+1) (IntegralMixedRoadmapGraph.ambient_eq hn ht ha hR0 _ q hc)) _
  have HC:HEq (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 (pair u label) q hv hc)
      (point hn ht ha hR0 u label q hv hc):=by
    unfold point
    exact cast_point_heq (congrArg (fun v :List Bool=>n v+4) (pairFst_pair u label)) _
  exact HA.symm.trans (HB.trans HC)

private theorem joined_transport (u v :List Bool) (H :u=v)
    (p q :Fin (n u+4)→ℝ) (a b :Fin (n v+4)→ℝ) (hp :HEq p a) (hq :HEq q b):
    JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u) p q ↔
      JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) v) a b:=by
  cases H
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

theorem incidence_iff_joined (u label q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=pair u label)
    (hd :IntegralMixedRoadmapAtomic.depth q=0)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q):
    IntegralMixedRoadmapAnchorIncidence.Incidence hn ht ha hR0 (pair u label) q ↔
      JoinedIn (IntegralMixedRoadmapGraph.firstZeroSet (n:=n) (t:=t) (R0:=R0) u)
        (point hn ht ha hR0 u label q hv hc) (prelude hn ht ha hR0 u q hv):=by
  have H:=IntegralMixedRoadmapAnchorIncidence.incidence_iff_joined_prelude hn ht ha hR0
    (pair u label) q hv hc hd hr
  have HP:HEq (IntegralMixedRoadmapGraph.pointAt hn ht ha hR0 (pair u label) q hv hc)
      (point hn ht ha hR0 u label q hv hc):=by
    unfold point
    exact cast_point_heq (congrArg (fun v :List Bool=>n v+4) (pairFst_pair u label)) _
  have HQ:HEq (IntegralMixedRoadmapGraph.preludeAt hn ht ha hR0 (pair u label) q hv hc)
      (prelude hn ht ha hR0 u q hv):=by
    unfold IntegralMixedRoadmapGraph.preludeAt prelude
    exact restriction_heq (congrArg (fun v :List Bool=>n v+4) (pairFst_pair u label)) _
  exact H.trans (joined_transport (n:=n) (t:=t) (R0:=R0) _ u (pairFst_pair u label) _ _ _ _ HP HQ)

private theorem marked_transport (u v :List Bool) (H :u=v)
    (z :BoundedRegularSource.Marked ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u))
    (p :Fin (n v+4)→ℝ) (hp :HEq z.val.val p):
    ∃w :BoundedRegularSource.Marked ((t v).finitePolynomial (n v))
      (t v).toData.size (t v).toData.size (R0 v),w.val.val=p:=by
  cases H
  exact ⟨z,eq_of_heq hp⟩

theorem prelude_marked (u label q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=pair u label)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q)
    (hg :AuxiliaryCandidateComponentCover.Good hn ht ha u label):
    ∃z :BoundedRegularSource.Marked ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u),
      z.val.val=prelude hn ht ha hR0 u q hv ∧
      (BoundedRegularSource.markedProjection _ _ _ _ z).val=
        IntegralMixedAuxiliaryCandidate.pointAt hn ht ha u label (Classical.choose hg):=by
  obtain ⟨_,z,HZ,_⟩:=IntegralMixedRoadmapGraph.preludeAt_marked hn ht ha hR0 (pair u label) q hv hc hr
  have HE:HEq z.val.val (prelude hn ht ha hR0 u q hv):=by
    have HH:HEq (IntegralMixedRoadmapGraph.preludeAt hn ht ha hR0 (pair u label) q hv hc)
        (prelude hn ht ha hR0 u q hv):=by
      unfold IntegralMixedRoadmapGraph.preludeAt prelude
      exact restriction_heq (congrArg (fun v :List Bool=>n v+4) (pairFst_pair u label)) _
    exact (heq_of_eq HZ).trans HH
  obtain ⟨w,HW⟩:=marked_transport (n:=n) (t:=t) (R0:=R0) _ u (pairFst_pair u label) z _ HE
  obtain ⟨hp,HP⟩:=IntegralMixedRoadmapGraph.preludeAt_projection hn ht ha hR0 (pair u label) q hv hc hr
  refine ⟨w,HW,funext fun i=>?_⟩
  rw [BoundedRegularSource.markedProjection_apply,HW]
  have HT:=HP ⟨i.val,by simpa only [pairFst_pair] using i.isLt⟩
  unfold IntegralMixedRoadmapGraph.preludeAt at HT
  unfold prelude IntegralMixedAuxiliaryCandidate.pointAt
  exact HT.trans (congrArg (IntegralMixedAuxiliaryCandidate.point hn ht ha (pair u label) hp) (Fin.ext rfl))

end LeanCanny.Connectivity.IntegralMixedRoadmapTwoAnchorGeometry
