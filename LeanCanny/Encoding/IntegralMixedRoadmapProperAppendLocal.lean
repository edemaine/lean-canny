/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalNear
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalBad
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCriticalFree
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalCoordinateComplete
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCriticalComplete
/-! # A genuine matched slab branch gives actual native local incidence -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "phi"=>IntegralMixedRoadmapProperParent.hom hn ht ha hR0 old hv hd
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "h"=>next d hk
local notation "hm"=>Nat.le_of_succ_le (IntegralMixedRoadmapProperParent.parent_room hn ht ha hR0 old hv hd)
local notation "rho"=>FrozenCoordinateOrdering.permutation (Frame.frozen (frame d hk))
local notation "CX"=>IntegralMixedCoordinateRename.state x rho
local notation "CR"=>cutRule x (Descriptor.frame d) h g hg
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "a"=>left.value V
local notation "b"=>right.value V

attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapProperParent.hom

/-- The constructed word itself satisfies Local. The interval hypotheses are
the genuine canonical bad-free and real-critical-free conditions; no native
guard, new word, interpreting hom or compatibility receipt is supplied. -/
theorem WordReceipt.local_of_matched_branch
    (hab :a<b)
    (M :MatchedSlabInterior x hm phi (frame d hk) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber :IntegralMixedSelectedPhysicalFiber.physical CX hm CR phi ((a+b)/2))
    {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u
      (M.curve fiber ((a+b)/2)∘(rho).symm) (M.curve fiber (if side then b else a)∘(rho).symm))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (havoid :∀v,v∈Set.Ioo a b→v∉IntegralMixedSelectedCriticalCuts.bad x hm CR phi
      (IntegralMixedRoadmapProperParent.choices hn ht ha hR0 old hv hd))
    (hheight :Disjoint (Set.Ioo a b)
      (realCriticalValues (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c)
        (line (d).frame h) V h)):
    IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word):=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  have hV:=W.atomic_valid hn ht ha hR0 old hv hd left right R side N hOld
  have HD :0<IntegralMixedRoadmapAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HB :IntegralMixedRoadmapProper.Base hn ht ha hR0 q:=
    ⟨HD,order_bounds_of_valid hn ht ha hR0 q hV HD,
      W.midpoint_companion hn ht ha hR0 old hv hd left right R side N,
      W.no_bad_of_canonical hn ht ha hR0 old hv hd left right R side N hV hOld hab havoid,
      W.original_order hn ht ha hR0 old hv hd left right R side N hV hab⟩
  have HF:=W.original_critical_free hn ht ha hR0 old hv hd left right R side N hV hOld hheight
  have HC:=IntegralMixedRoadmapProperCritical.noCritical_of_original_critical_free hn ht ha hR0 q hV HD HF
  have HA:=IntegralMixedRoadmapLocalEdge.allCoordinates_of_coordinate_meaning hn ht ha hR0 side q hV HB
    (fun j hj hjn=>W.coordinate_meaning_of_matched_branch hn ht ha hR0 old hv hd left right R side
      hab M fiber N hV hOld j (by simpa only [q,depth_packet] using hj)
      (by simpa only [q,dimension_packet] using hjn))
  refine ⟨hV,HB,HC,?_⟩
  cases side
  · exact Or.inl HA
  · exact Or.inr HA

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
