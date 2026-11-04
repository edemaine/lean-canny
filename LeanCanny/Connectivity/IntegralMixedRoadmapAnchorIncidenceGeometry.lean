/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapMarkedTargetAttachment
public import LeanCanny.Connectivity.IntegralMixedRoadmapMarkedComponents
/-! # The native anchor search identifies the bound marked component -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapGraph
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.levels
  pointAt preludeAt

theorem incidence_iff_joined_prelude (candidate seed :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 seed)
    (hc :IntegralMixedRoadmapAtomic.candidate seed=candidate)
    (hd :IntegralMixedRoadmapAtomic.depth seed=0)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 seed):
    Incidence hn ht ha hR0 candidate seed ↔
      JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) candidate)
        (pointAt hn ht ha hR0 candidate seed hv hc) (preludeAt hn ht ha hR0 candidate seed hv hc):=by
  constructor
  · rintro ⟨terminal,HMarker,HRaw⟩
    have hTerminal:=HRaw.2.1
    have hcTerminal:=HRaw.2.2.2.1
    have HMarkerMeaning:=(markerAt_iff hn ht ha hR0 candidate terminal hTerminal hcTerminal).mp HMarker
    have HNative:=raw_reachable_joined hn ht ha hR0 candidate seed terminal HRaw
    have HJoined:JoinedIn (zeroSet (n:=n) (t:=t) (R0:=R0) candidate)
        (pointAt hn ht ha hR0 candidate seed hv hc)
        (preludeAt hn ht ha hR0 candidate terminal hTerminal hcTerminal):=by
      simpa only [HMarkerMeaning.2.2] using HNative
    exact HJoined.trans (preludeAt_joined_same_candidate hn ht ha hR0 candidate seed terminal
      hv hTerminal hc hcTerminal hr HMarkerMeaning.2.1).symm
  · intro HJoined
    have HZero:frozenSlice (n:=n) (t:=t) (R0:=R0) candidate (IntegralMixedRoadmapAtomic.depth seed)
        (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 seed hv)=zeroSet (n:=n) (t:=t) (R0:=R0) candidate:=by
      ext point
      constructor
      · exact fun H=>H.1
      · intro H
        refine ⟨H,?_⟩
        intro i hi
        rw [hd] at hi
        exact False.elim (Nat.not_lt_zero _ hi)
    exact IntegralMixedRoadmapProperAppend.incidence_of_prelude_path hn ht ha hR0 candidate seed hv hc hr
      (by simpa only [HZero] using HJoined)

theorem packet_iff (candidate seed :List Bool):
    pair candidate seed∈language hn ht ha hR0 ↔Incidence hn ht ha hR0 candidate seed:=by
  simp only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

end LeanCanny.Connectivity.IntegralMixedRoadmapAnchorIncidence
