/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapMarkedPointAt
public import LeanCanny.Geometry.BoundedMarkedCoordinates
/-! # Replay-bound marked phases over one candidate are joined -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open Set LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapMarkedPrelude.value
  IntegralMixedRoadmapMarkedPrelude.point preludeAt IntegralMixedAuxiliaryCandidate.point

private theorem marked_transport (u v :List Bool) (h :u=v)
    (z :BoundedRegularSource.Marked ((t u).finitePolynomial (n u))
      (t u).toData.size (t u).toData.size (R0 u))
    (p :Fin (n v+4)→ℝ) (he :HEq z.val.val p):
    ∃w :BoundedRegularSource.Marked ((t v).finitePolynomial (n v))
      (t v).toData.size (t v).toData.size (R0 v),w.val.val=p:=by
  cases h
  exact ⟨z,eq_of_heq he⟩

/-- Actual marked membership is retained, including its native slack phase.
Only the original input index is transported to the fixed candidate domain. -/
theorem preludeAt_marked (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c) (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q):
    ∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha c,
    ∃z :BoundedRegularSource.Marked ((t (pairFst c)).finitePolynomial (n (pairFst c)))
      (t (pairFst c)).toData.size (t (pairFst c)).toData.size (R0 (pairFst c)),
      z.val.val=preludeAt hn ht ha hR0 c q hv hc ∧
      (BoundedRegularSource.markedProjection _ _ _ _ z).val=IntegralMixedAuxiliaryCandidate.point hn ht ha c hp:=by
  obtain ⟨_,z,HZ,_⟩:=IntegralMixedRoadmapMarkedPrelude.exists_marked hn ht ha hR0 q hv hr
  have HO:IntegralMixedAuxiliaryMarkedIntegerSource.original (IntegralMixedRoadmapAtomic.root q)=pairFst c:=
    (IntegralMixedRoadmapMarkedPrelude.original_root q).trans (congrArg pairFst hc)
  have HPoint:HEq z.val.val (preludeAt hn ht ha hR0 c q hv hc):=
    (heq_of_eq HZ).trans (preludeAt_heq hn ht ha hR0 c q hv hc)
  obtain ⟨w,HW⟩:=marked_transport (n:=n) (t:=t) (R0:=R0) _ _ HO z _ HPoint
  obtain ⟨hp,HP⟩:=preludeAt_projection hn ht ha hR0 c q hv hc hr
  refine ⟨hp,w,HW,?_⟩
  funext i
  rw [BoundedRegularSource.markedProjection_apply,HW]
  exact HP i

/-- Slack phases need not agree. Both marked points attach to the lift of
exactly the same original candidate point, inside the same regular source. -/
theorem preludeAt_joined_same_candidate (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (hrA :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 a)
    (hrB :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 b):
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (preludeAt hn ht ha hR0 c a hA hc) (preludeAt hn ht ha hR0 c b hB hd):=by
  obtain ⟨hp,z,HZ,HP⟩:=preludeAt_marked hn ht ha hR0 c a hA hc hrA
  obtain ⟨hp',w,HW,HP'⟩:=preludeAt_marked hn ht ha hR0 c b hB hd hrB
  have HE:BoundedRegularSource.markedProjection _ _ _ _ z=BoundedRegularSource.markedProjection _ _ _ _ w:=
    Subtype.ext (HP.trans HP'.symm)
  have JZ:=BoundedRegularSource.joined_to_lift _ _ _ _ z
  have JW:=BoundedRegularSource.joined_to_lift _ _ _ _ w
  rw [HE] at JZ
  have J:=JZ.trans JW.symm
  have JP:JoinedIn {p |(BoundedRegularSource.polynomial ((t (pairFst c)).finitePolynomial (n (pairFst c)))
      (t (pairFst c)).toData.size (t (pairFst c)).toData.size (R0 (pairFst c))).eval₂ (Int.castRingHom ℝ) p=0}
      z.val.val w.val.val:=(joinedIn_iff_joined z.val.property w.val.property).mpr J
  rw [HZ,HW] at JP
  have HS:zeroSet (n:=n) (t:=t) (R0:=R0) c={p |
      (BoundedRegularSource.polynomial ((t (pairFst c)).finitePolynomial (n (pairFst c)))
        (t (pairFst c)).toData.size (t (pairFst c)).toData.size (R0 (pairFst c))).eval₂ (Int.castRingHom ℝ) p=0}:=by
    unfold zeroSet originalSource
    rw [IntegralMixedOriginalRegularSource.source_polynomial]
  exact HS.symm ▸ JP

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
