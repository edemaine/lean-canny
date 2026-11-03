/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
/-! # A reserved interval endpoint is the same terminal bank field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutEndpointField
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedPhysicalCutOpenInterval (selected Bounds)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem square_point (A : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan A)
    (J : IntegralMixedFramedHistoryFamilyBits.Data A E) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs A E L F C) (key : List Bool→List Bool)
    (hp : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family A E J).birth (key c)) (c v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input A E J L F C hs key hp) c v)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family A E J).birth (key c))) :
    IntegralFramedPhysicalSquare.point A E J L F C hs key hp c v hv i=
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point ((IntegralMixedFramedHistoryFamilyBits.family A E J).state (key c))
        (IntegralFramedPhysicalSquare.scalarTuple A E J L F C hs key hp c v hv) i:=rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralFramedPhysicalSquare.point
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
variable (q w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) q w)

theorem endpoint_point (side : Bool)
    (hi : selected side q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false q) :
    IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false side q w hv hi=
      IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv
        ⟨selected side q,hi⟩:=
 (square_point P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv _).symm

theorem endpoint_field (side : Bool)
    (hi : selected side q<IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false q) :
    IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false side q w hv hi=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0) q w hv (selected side q):=by
 have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) q=
     IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false q:=rfl
 rw [endpoint_point hn ht ha hR0 q w hv side hi]
 unfold IntegralMixedPhysicalFieldEquality.pointNewest
 apply congrArg _
 apply Fin.ext
 change selected side q=min (selected side q) (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) q-1)
 rw [HC,min_eq_left (by omega :selected side q≤IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false q-1)]

end LeanCanny.Encoding.IntegralMixedPhysicalCutEndpointField
