/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateComplete
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
/-! # Geometric coordinate certificates satisfy the actual bounded scan -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension

theorem allCoordinates_of_coordinate_meaning (right : Bool) (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HM : ∀j,IntegralMixedRoadmapAtomic.depth q≤j→j≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q→
      IntegralMixedRoadmapProperRow.CoordinateMeaning hn ht ha hR0 right q j hv) :
    allCoordinates hn ht ha hR0 right q :=by
  intro i hi
  have HD:=HB.1
  have HFit : IntegralMixedRoadmapAtomic.depth q+i≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q:=by
    unfold count IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex at hi
    omega
  have H:=IntegralMixedRoadmapProperRow.holds_of_coordinate_meaning hn ht ha hR0 right q
    (IntegralMixedRoadmapAtomic.depth q+i) hv HB (Nat.le_add_right _ _) HFit
    (HM _ (Nat.le_add_right _ _) HFit)
  simpa only [coordinateKey,pairFst_pair,pairSnd_pair,List.length_replicate] using H

end LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
