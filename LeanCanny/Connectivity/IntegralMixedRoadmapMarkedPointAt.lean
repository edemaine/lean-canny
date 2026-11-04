/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkedPreludeRetention
public import LeanCanny.Encoding.IntegralMixedRoadmapMarkerAt
public import LeanCanny.Connectivity.IntegralMixedRoadmapFrozenSliceTransport
/-! # A fixed-candidate marked target across independently sampled histories -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedOriginalRegularSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapMarkedPrelude.value
  IntegralMixedRoadmapMarkedPrelude.point originalSource

noncomputable def preludeAt (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (_hc :IntegralMixedRoadmapAtomic.candidate q=c):Fin (n (pairFst c)+3+1)→ℝ:=
  fun i=>IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 q hv i.val

private theorem restriction_heq {a b :ℕ} (h :a=b) (v :ℕ→ℝ):
    HEq (fun i:Fin a=>v i.val) (fun i:Fin b=>v i.val):=by cases h;rfl
private theorem cast_point_heq {a b :ℕ} (h :a=b) (p :Fin a→ℝ):
    HEq p (fun i:Fin b=>p (Fin.cast h.symm i)):=by cases h;rfl

theorem prelude_dimension (c q :List Bool) (hc :IntegralMixedRoadmapAtomic.candidate q=c):
    IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapAtomic.root q)+3=n (pairFst c)+3:=by
  rw [IntegralMixedRoadmapMarkedPrelude.number_root]
  exact congrArg (fun v=>n (pairFst v)+3) hc

theorem preludeAt_heq (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c):
    HEq (IntegralMixedRoadmapMarkedPrelude.point hn ht ha hR0 q hv) (preludeAt hn ht ha hR0 c q hv hc):=by
  unfold IntegralMixedRoadmapMarkedPrelude.point preludeAt
  exact restriction_heq (congrArg (·+1) (prelude_dimension (n:=n) c q hc)) _

private theorem zero_transport {a b :ℕ} (P :SpatialSource a) (Q :SpatialSource b)
    (hab :a=b) (hs :HEq P Q) (p :Fin (a+1)→ℝ) (q :Fin (b+1)→ℝ) (hp :HEq p q)
    (hz :(FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0):
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) q=0:=by
  subst b
  cases eq_of_heq hs
  cases eq_of_heq hp
  exact hz

theorem preludeAt_zero (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c) (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q):
    preludeAt hn ht ha hR0 c q hv hc∈zeroSet (n:=n) (t:=t) (R0:=R0) c:=by
  have HO :IntegralMixedAuxiliaryMarkedIntegerSource.original (IntegralMixedRoadmapAtomic.root q)=pairFst c:=
    (IntegralMixedRoadmapMarkedPrelude.original_root q).trans (congrArg pairFst hc)
  have HS:HEq (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (IntegralMixedRoadmapAtomic.root q))
      (originalSource (n:=n) (t:=t) (R0:=R0) c):=by
    unfold originalSource
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    exact IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO
  exact zero_transport _ _ (prelude_dimension (n:=n) c q hc) HS _ _
    (preludeAt_heq hn ht ha hR0 c q hv hc) (IntegralMixedRoadmapMarkedPrelude.point_source_zero hn ht ha hR0 q hv hr)

theorem markerAt_iff (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c):
    q∈IntegralMixedRoadmapMarkerAt.language hn ht ha hR0 ↔
      IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q ∧
      IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q ∧
      pointAt hn ht ha hR0 c q hv hc=preludeAt hn ht ha hR0 c q hv hc:=by
  have HA:HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 q hv) (pointAt hn ht ha hR0 c q hv hc):=by
    unfold pointAt
    exact cast_point_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 c q hc)) _
  have HM:=preludeAt_heq hn ht ha hR0 c q hv hc
  rw [IntegralMixedRoadmapMarkerAt.language_iff hn ht ha hR0 q hv]
  constructor
  · rintro ⟨HD,HR,HE⟩
    exact ⟨HD,HR,eq_of_heq (HA.symm.trans (HE.trans HM))⟩
  · rintro ⟨HD,HR,HE⟩
    exact ⟨HD,HR,HA.trans ((heq_of_eq HE).trans HM.symm)⟩

/-- The target vector stays fixed as histories grow; only actual field values
are compared. The histories' own complete words may be different. -/
theorem preludeAt_eq_of_fields (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (he :∀i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a,
      IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 a hA i=
      IntegralMixedRoadmapMarkedPrelude.value hn ht ha hR0 b hB i):
    preludeAt hn ht ha hR0 c a hA hc=preludeAt hn ht ha hR0 c b hB hd:=by
  have HD:IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a=n (pairFst c)+3:=by
    rw [IntegralMixedRoadmapAtomic.dimension_eq]
    exact congrArg (fun v=>n (pairFst v)+3) hc
  funext i
  exact he i.val (by have HI:=i.isLt;omega)

/-- The first original coordinates are the supplied candidate, while the
remaining four coordinates retain the actual native marked-lift phase. -/
theorem preludeAt_projection (c q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c) (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 q):
    ∃hp :IntegralMixedAuxiliaryCandidate.Valid hn ht ha c,∀i :Fin (n (pairFst c)),
      preludeAt hn ht ha hR0 c q hv hc (i.castAdd 4)=IntegralMixedAuxiliaryCandidate.point hn ht ha c hp i:=by
  have HO:=IntegralMixedRoadmapMarkedPrelude.original_coordinates hn ht ha hR0 q hv hr
  rw [hc] at HO
  obtain ⟨hp,HE⟩:=HO
  exact ⟨hp,fun i=>(HE i).symm⟩

theorem replay_of_preludeAt_eq (c a b :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (hc :IntegralMixedRoadmapAtomic.candidate a=c) (hd :IntegralMixedRoadmapAtomic.candidate b=c)
    (hr :IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 a)
    (he :preludeAt hn ht ha hR0 c a hA hc=preludeAt hn ht ha hR0 c b hB hd):
    IntegralMixedRoadmapMarkedPrelude.Replay hn ht ha hR0 b:=by
  apply IntegralMixedRoadmapMarkedPrelude.replay_of_values hn ht ha hR0 a b hA hB (hc.trans hd.symm) hr
  intro i hi
  have HD:IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 a=n (pairFst c)+3:=by
    rw [IntegralMixedRoadmapAtomic.dimension_eq]
    exact congrArg (fun v=>n (pairFst v)+3) hc
  exact congrFun he ⟨i,by omega⟩

local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "E" old=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "F" old=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "R" old=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old (E old)

/-- The next target height is already present in the canonical parent bank.
No root choice, criticality premise, or new producer is needed. -/
theorem prelude_target_reference (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (q :Fin ((P).ambient (R old)+1)→ℝ)
    (HPoint:canonicalPointAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old rfl q=
      preludeAt hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl):
    ∃ref :Fin (IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd (E old) (F old)).length,
      q (IntegralMixedChronologicalSweepFrame.next
        (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (E old) (F old))
        (IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd (E old) (F old)))=
      IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd (E old) (F old) ref:=by
  let coord:=childCoordinate hn ht ha hR0 (IntegralMixedRoadmapAtomic.candidate old) old hv rfl
  have HH:=congrFun HPoint coord
  have HNext:Fin.cast (congrArg (·+1) (canonical_ambient_eq hn ht ha hR0
      (IntegralMixedRoadmapAtomic.candidate old) old rfl)).symm coord=
      IntegralMixedChronologicalSweepFrame.next
        (IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd (E old) (F old))
        (IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd (E old) (F old)):=by
    apply Fin.ext
    change IntegralMixedRoadmapAtomic.depth old=_
    exact (IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd (E old) (F old)).symm
  unfold canonicalPointAt preludeAt at HH
  rw [HNext] at HH
  let hi:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 old hv
  refine ⟨IntegralMixedRoadmapMarkedPrelude.parentIndex hn ht ha hR0 old hv hd (E old) (F old)
    (IntegralMixedRoadmapAtomic.depth old) hi,?_⟩
  exact HH.trans (IntegralMixedRoadmapMarkedPrelude.canonical_value hn ht ha hR0 old hv hd (E old) (F old)
    (IntegralMixedRoadmapAtomic.depth old) hi).symm

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
