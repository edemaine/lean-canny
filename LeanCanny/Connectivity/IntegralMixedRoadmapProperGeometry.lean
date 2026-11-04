/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapGraphGeometry
public import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureReadback
public import LeanCanny.Connectivity.IntegralMixedRoadmapLocalPath
/-! # Transport native proper paths to one original candidate source -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.source
 IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapProper.midpointPoint

theorem dimension_original_eq (c q : List Bool) (hc : IntegralMixedRoadmapAtomic.candidate q=c) :
    D q=n (pairFst c)+3 :=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 q]
  exact congrArg (fun w : List Bool=>n (pairFst w)+3) hc

noncomputable def midpointAt (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c) : Fin (n (pairFst c)+3+1)→ℝ:=fun i=>
  IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv
    (Fin.cast (congrArg (·+1) (dimension_original_eq hn ht ha hR0 c q hc)).symm i)

private theorem cast_heq {a b : ℕ} (H : a=b) (p : Fin a→ℝ) :
    HEq p (fun i : Fin b=>p (Fin.cast H.symm i)) :=by cases H;rfl

theorem proper_midpointAt_eq (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (H : IntegralMixedRoadmapEdge.Proper hn ht ha hR0 (pair a b)) :
    midpointAt hn ht ha hR0 c a hA hc=midpointAt hn ht ha hR0 c b hB hd :=by
  have HA : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 a hA) (midpointAt hn ht ha hR0 c a hA hc):=
    cast_heq (congrArg (·+1) (dimension_original_eq hn ht ha hR0 c a hc)) _
  have HB : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 b hB) (midpointAt hn ht ha hR0 c b hB hd):=
    cast_heq (congrArg (·+1) (dimension_original_eq hn ht ha hR0 c b hd)) _
  exact eq_of_heq (HA.symm.trans ((IntegralMixedRoadmapProperMidSignature.proper_midpoint_eq hn ht ha hR0 a b hA hB H).trans HB))


private theorem zero_set_heq {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b) (HD : a=b) (HS : HEq P Q) :
    HEq ({p : (Fin (a+1)→ℝ) | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0} : Set _)
      ({p : (Fin (b+1)→ℝ) | (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0} : Set _) :=by
  cases HD
  have H : P=Q:=eq_of_heq HS
  cases H
  rfl

private theorem joined_heq {a b : ℕ} (s : Set (Fin a→ℝ)) (t : Set (Fin b→ℝ))
    (HD : a=b) (HS : HEq s t) (p q : Fin a→ℝ) (r u : Fin b→ℝ)
    (HP : HEq p r) (HQ : HEq q u) (H : JoinedIn s p q) : JoinedIn t r u :=by
  cases HD
  have HE : s=t:=eq_of_heq HS
  have HEP : p=r:=eq_of_heq HP
  have HEQ : q=u:=eq_of_heq HQ
  simpa only [←HE,←HEP,←HEQ] using H

private theorem prepared_path_original (c q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc : IntegralMixedRoadmapAtomic.candidate q=c)
    (H : JoinedIn
      {p : Fin (IntegralMixedRoadmapLocalFrame.ambient hn ht ha hR0 q+1)→ℝ |
        (FermatCriticalHomogenization.polynomial
          ((IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data).spatial
            (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).low
          ((IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data).spatial
            (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).leading
          ((IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data).spatial
            (IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q)).degree).eval₂ (Int.castRingHom ℝ) p=0}
      (IntegralMixedRoadmapLocalFrame.child hn ht ha hR0 q hv)
      (IntegralMixedRoadmapLocalFrame.midpoint hn ht ha hR0 q hv)) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c) (pointAt hn ht ha hR0 c q hv hc) (midpointAt hn ht ha hR0 c q hv hc) :=by
  let K:=IntegralMixedRoadmapLocalFrame.oldKey hn ht ha hR0 q
  let P:=(IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data).spatial K
  have HD : IntegralMixedRoadmapLocalFrame.ambient hn ht ha hR0 q=n (pairFst c)+3:=
    (IntegralMixedRoadmapLocalFrame.ambient_eq hn ht ha hR0 q).trans (dimension_original_eq hn ht ha hR0 c q hc)
  have HS:=IntegralMixedPhysicalOriginalSource.family_source hn ht ha hR0 false K
  have HO : IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst K)=pairFst c:=by
    unfold K IntegralMixedRoadmapLocalFrame.oldKey
    rw [IntegralMixedRoadmapProperRow.parentKey_root]
    simpa only [IntegralMixedRoadmapProperRow.root,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair,
      IntegralMixedRoadmapProperRow.atomic,IntegralMixedRoadmapLocalFrame.rowKey] using congrArg pairFst hc
  have HSfixed:=HS.trans (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO)
  have Hset : HEq ({p : (Fin (IntegralMixedRoadmapLocalFrame.ambient hn ht ha hR0 q+1)→ℝ) |
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0} : Set _)
      (zeroSet (n:=n) (t:=t) (R0:=R0) c):=
    zero_set_heq P (originalSource (n:=n) (t:=t) (R0:=R0) c) HD HSfixed
  have HC0 : HEq (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv)
      (IntegralMixedRoadmapLocalFrame.child hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapLocalFrame.child
    exact cast_heq (congrArg (·+1) (IntegralMixedRoadmapLocalFrame.ambient_eq hn ht ha hR0 q).symm)
        (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv)
  have HM0 : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv)
      (IntegralMixedRoadmapLocalFrame.midpoint hn ht ha hR0 q hv):=by
    unfold IntegralMixedRoadmapLocalFrame.midpoint
    exact cast_heq (congrArg (·+1) (IntegralMixedRoadmapLocalFrame.ambient_eq hn ht ha hR0 q).symm)
        (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv)
  have HI : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) (IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv):=
    cast_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q))
      (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv)
  have HP : HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) (pointAt hn ht ha hR0 c q hv hc):=
    cast_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c q hc)) _
  have HM : HEq (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv) (midpointAt hn ht ha hR0 c q hv hc):=
    cast_heq (congrArg (·+1) (dimension_original_eq hn ht ha hR0 c q hc)) _
  exact joined_heq _ _ (congrArg (·+1) HD) Hset _ _ _ _
    (HC0.symm.trans (HI.symm.trans HP)) (HM0.symm.trans HM) H

attribute [local irreducible] midpointAt pointAt zeroSet

/-- Every native proper edge gives a path through its actual shared midpoint. -/
theorem proper_joined (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (H : IntegralMixedRoadmapEdge.Proper hn ht ha hR0 (pair a b)) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=by
  have HLa : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 a:=by
    simpa only [pairFst_pair] using H.2.1
  have HLb : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 b:=by
    simpa only [pairSnd_pair] using H.2.2.1
  have HA:=prepared_path_original hn ht ha hR0 c a hA hc
    (IntegralMixedRoadmapLocalFrame.local_joined hn ht ha hR0 a HLa)
  have HB:=prepared_path_original hn ht ha hR0 c b hB hd
    (IntegralMixedRoadmapLocalFrame.local_joined hn ht ha hR0 b HLb)
  rw [proper_midpointAt_eq hn ht ha hR0 c a b hA hB hc hd H] at HA
  exact HA.trans HB.symm

theorem adjacent_joined (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c) (hd : IntegralMixedRoadmapAtomic.candidate b=c)
    (H : IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0 a b) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=by
  rcases H with HI|HP
  · exact identity_joined hn ht ha hR0 c a b hA hB hc hd HI
  · exact proper_joined hn ht ha hR0 c a b hA hB hc hd HP

theorem path_joined (c a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hc : IntegralMixedRoadmapAtomic.candidate a=c)
    (H : Relation.ReflTransGen (IntegralMixedRoadmapEdge.Adjacent hn ht ha hR0) a b)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) (hd : IntegralMixedRoadmapAtomic.candidate b=c) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a hA hc) (pointAt hn ht ha hR0 c b hB hd) :=by
  revert hB hd
  induction H with
  | refl=>
    intro hB hd
    exact JoinedIn.refl (show pointAt hn ht ha hR0 c a hA hc∈zeroSet (n:=n) (t:=t) (R0:=R0) c from
      (pointAt_mem hn ht ha hR0 c a hA hc).1)
  | @tail b d Hab Hbd IH=>
    intro hD hCd
    have HB:= (IntegralMixedRoadmapEdge.valid hn ht ha hR0 b d Hbd).1
    have HC : IntegralMixedRoadmapAtomic.candidate b=c:=
      (path_candidate_eq hn ht ha hR0 a b Hab).symm.trans hc
    exact (IH HB HC).trans (adjacent_joined hn ht ha hR0 c b d HB hD HC hCd Hbd)

theorem raw_reachable_joined (c a b : List Bool) (H : RawReachable hn ht ha hR0 c a b) :
    JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) c)
      (pointAt hn ht ha hR0 c a H.1 H.2.2.1) (pointAt hn ht ha hR0 c b H.2.1 H.2.2.2.1) :=
  path_joined hn ht ha hR0 c a b H.1 H.2.2.1 H.2.2.2.2 H.2.1 H.2.2.2.1

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
