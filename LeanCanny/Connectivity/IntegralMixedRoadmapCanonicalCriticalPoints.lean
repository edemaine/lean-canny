/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedRoadmapFrozenSliceTransport
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCanonicalEndpoints
public import LeanCanny.Geometry.IntegralMixedJointSlabEndpointSet
/-! # Accepted representatives are genuine critical points in the canonical slice -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedRoadmapGraph
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem occurrence_cast_back {a b k :ℕ} (V :SpatialSource a) (W :SpatialSource b)
    (HD :a=b) (HS :HEq V W) (levels :ℕ→ℝ) (p :Fin (a+1)→ℝ)
    (H :IntegralMixedAtomicOccurrence.Occurrence W k levels
      (fun i=>p (Fin.cast (congrArg (·+1) HD).symm i))) :
    IntegralMixedAtomicOccurrence.Occurrence V k levels p:=by
  cases HD
  cases eq_of_heq HS
  exact H

private theorem occurrence_depth {a k l :ℕ} (V :SpatialSource a) (levels :ℕ→ℝ)
    (p :Fin (a+1)→ℝ) (H :k=l) (HO :IntegralMixedAtomicOccurrence.Occurrence V k levels p):
    IntegralMixedAtomicOccurrence.Occurrence V l levels p:=by
  cases H
  exact HO

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "r"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
local notation "c"=>IntegralMixedRoadmapAtomic.candidate old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.point IntegralMixedRoadmapAtomic.levels
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentCommands

include hv in
/-- An actual accepted representative gives its full critical occurrence after
the proved canonical coordinate cast. Neither fields nor gradients are assumed. -/
theorem canonical_occurrence_of_pointAt (q :List Bool)
    (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c)
    (hk :IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old)
    (p :Fin ((P).ambient r+1)→ℝ)
    (hp :canonicalPointAt hn ht ha hR0 c old rfl p=pointAt hn ht ha hR0 c q hq hc):
    IntegralMixedAtomicOccurrence.Occurrence Q (IntegralMixedRoadmapAtomic.depth old)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hq) p:=by
  have HO:=pointAt_occurrence hn ht ha hR0 c q hq hc
  have HP:=Eq.mpr (congrArg
    (fun z=>IntegralMixedAtomicOccurrence.Occurrence (originalSource (n:=n) (t:=t) (R0:=R0) c)
      (IntegralMixedRoadmapAtomic.depth q) (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hq) z) hp) HO
  have HS :HEq Q (originalSource (n:=n) (t:=t) (R0:=R0) c):=
    (IntegralMixedRoadmapRetainedAppend.own_source_heq hn ht ha hR0 old hv).symm.trans
      (IntegralMixedRoadmapAtomic.source_original hn ht ha hR0 old hv)
  have HC:=occurrence_cast_back Q (originalSource (n:=n) (t:=t) (R0:=R0) c)
    (canonical_ambient_eq hn ht ha hR0 c old rfl) HS
    (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hq) p HP
  exact occurrence_depth Q _ p hk HC

variable (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "hfit"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hfit
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
noncomputable local instance canonicalCriticalPointsIndexFintype :
    Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) cs):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) cs

/-- Its current height is an actual real critical value, witnessed by p itself. -/
theorem canonical_height_mem_realCriticalValues (q :List Bool)
    (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c)
    (hk :IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old)
    (p :Fin ((P).ambient r+1)→ℝ)
    (hp :canonicalPointAt hn ht ha hR0 c old rfl p=pointAt hn ht ha hR0 c q hq hc)
    (hSlice :p∈slice Q (d).frame V):
    p h∈realCriticalValues Q (line (d).frame h) V h:=by
  have HO:=canonical_occurrence_of_pointAt hn ht ha hR0 old hv q hq hc hk p hp
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  apply (line_realCriticalValues_iff Q (d).frame V h
    (IntegralMixedChronologicalSweepFrame.next_free d hfit) (d).free_normal (p h)).mpr
  refine ⟨p,hSlice,rfl,?_⟩
  intro i hi hih
  have HI :IntegralMixedRoadmapAtomic.depth old ≤ i.val:=by
    have HF :¬i.val<(d).labels.length:=fun H=>hi (((d).frozen_mem i).mpr H)
    omega
  have HNe :i.val≠IntegralMixedRoadmapAtomic.depth old:=by
    intro HE
    apply hih
    apply Fin.ext
    exact HE.trans HL.symm
  exact HO.critical i HI HNe

/-- This uses the genuine critical-value summand, not an auxiliary ghost root. -/
theorem canonical_height_mem_jointEndpointSet (q :List Bool)
    (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c)
    (hk :IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old)
    (p :Fin ((P).ambient r+1)→ℝ)
    (hp :canonicalPointAt hn ht ha hR0 c old rfl p=pointAt hn ht ha hR0 c q hq hc)
    (hSlice :p∈slice Q (d).frame V):
    p h∈jointEndpointSet x hm phi (d).frame h g hg V
      (IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd):=
  Or.inr (canonical_height_mem_realCriticalValues hn ht ha hR0 old hv hd q hq hc hk p hp hSlice)

/-- Freezing h weakens the accepted h-critical equations. In particular they
hold at all child free coordinates outside the next objective g. -/
theorem canonical_child_partials (q :List Bool)
    (hq :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hc :IntegralMixedRoadmapAtomic.candidate q=c)
    (hk :IntegralMixedRoadmapAtomic.depth q=IntegralMixedRoadmapAtomic.depth old)
    (p :Fin ((P).ambient r+1)→ℝ)
    (hp :canonicalPointAt hn ht ha hR0 c old rfl p=pointAt hn ht ha hR0 c q hq hc):
    ∀i,i∉(line (d).frame h).frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q).low (Q).leading (Q).degree)).eval₂
        (Int.castRingHom ℝ) p=0:=by
  have HO:=canonical_occurrence_of_pointAt hn ht ha hR0 old hv q hq hc hk p hp
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  intro i hi _
  have HF:=(IntegralMixedChronologicalSweepFrame.free_iff d hfit i).mp hi
  have HI :IntegralMixedRoadmapAtomic.depth old < i.val:=by omega
  exact HO.critical i HI.le (Nat.ne_of_gt HI)

end LeanCanny.Connectivity.IntegralMixedRoadmapGraph
