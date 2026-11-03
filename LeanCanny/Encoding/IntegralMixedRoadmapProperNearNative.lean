/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowQuery
public import LeanCanny.Encoding.IntegralFramedPhysicalNearGuard
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticSpace
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest

/-! # Original-only Near and zero-parameter midpoint statistic machines

Every query uses its literal prepared ordinary or mean-centered cut root.
Its full word is an independent argument, never a copied ordinal word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "A"=>IntegralMixedPhysicalMarkedPlan.native hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "hT"=>IntegralMixedPhysicalMarkedPlan.tables_native hn ht ha (radius_binary hR0) false
local notation "hr"=>IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.native
  IntegralMixedPhysicalMarkedPlan.tables IntegralMixedFramedHistoryFamilyBits.family
  dimension initial parent terminal IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

noncomputable def count (mean : Bool) (z : List Bool):=
  (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (terminal hn ht ha hR0 mean z)).count
theorem count_unary (mean : Bool) : UnaryFn (count hn ht ha hR0 mean):=
  (IntegralMixedFramedBankSnapshotBits.count_unary (B).parameters (A).parameters (B).plan (B).data).comp
    (terminal_FP hn ht ha hR0 mean)

noncomputable def pointProducer (mid : Bool) (z : List Bool):=if mid then
  IntegralMixedRoadmapProper.midProducer (dimension hn ht ha hR0 z) (initial hn ht ha hR0 z) (atomic z) (coordinate z)
  else IntegralMixedRoadmapProper.childProducer (dimension hn ht ha hR0 z) (initial hn ht ha hR0 z) (atomic z) (coordinate z)

theorem pointProducer_binary (mid : Bool) : BinaryFn (pointProducer hn ht ha hR0 mid):=by
  have HM:=((IntegralMixedRoadmapProper.midFirst_unary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)
    (IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0)).comp atomic_FP)
  have HC:=((IntegralMixedRoadmapAtomic.first_unary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)
    (IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0)).comp atomic_FP)
  have HM' : UnaryFn (fun z=>IntegralMixedRoadmapProper.midFirst (dimension hn ht ha hR0 z)
      (initial hn ht ha hR0 z) (atomic z)):=by
    simpa only [dimension,initial] using HM
  have HC' : UnaryFn (fun z=>IntegralMixedRoadmapAtomic.first (dimension hn ht ha hR0 z)
      (initial hn ht ha hR0 z) (atomic z)):=by
    simpa only [dimension,initial] using HC
  have HJ:=((BinaryFn.ofUnary (dimension_unary hn ht ha hR0)).sub coordinate_binary)
  cases mid
  · change BinaryFn (fun z=>IntegralMixedRoadmapAtomic.first (dimension hn ht ha hR0 z)
      (initial hn ht ha hR0 z) (atomic z)+(dimension hn ht ha hR0 z-coordinate z))
    exact (BinaryFn.ofUnary HC').add HJ
  · change BinaryFn (fun z=>IntegralMixedRoadmapProper.midFirst (dimension hn ht ha hR0 z)
      (initial hn ht ha hR0 z) (atomic z)+(dimension hn ht ha hR0 z-coordinate z))
    exact (BinaryFn.ofUnary HM').add HJ

noncomputable def pointIndex (mean mid : Bool) (z : List Bool):=count hn ht ha hR0 mean z-1-pointProducer hn ht ha hR0 mid z
noncomputable def centerIndex (right : Bool) (z : List Bool):=count hn ht ha hR0 false z-1-oldProducer right z

theorem pointIndex_binary (mean mid : Bool) : BinaryFn (pointIndex hn ht ha hR0 mean mid):=
  ((BinaryFn.ofUnary (count_unary hn ht ha hR0 mean)).sub (BinaryFn.const 1)).sub (pointProducer_binary hn ht ha hR0 mid)
theorem centerIndex_binary (right : Bool) : BinaryFn (centerIndex hn ht ha hR0 right):=
  ((BinaryFn.ofUnary (count_unary hn ht ha hR0 false)).sub (BinaryFn.const 1)).sub (oldProducer_binary right)

theorem metadata : IntegralMixedVirtualQueryBits.InputMetadata
    (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data) :=IntegralMixedFramedPhysicalBits.virtualInputMetadata (B).parameters (A).parameters
  (B).plan (B).data T hT hr

theorem sampler_access (mean : Bool) :
    (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)).Access :=
  IntegralFramedPhysicalSquare.native_access (B).parameters (A).parameters (B).plan (B).data T hT hr
    (B).nodes (B).factor (B).seed (B).bounds (A).nodes (A).factor (A).seed
    (terminal hn ht ha hR0 mean) (terminal_FP hn ht ha hR0 mean) (positive hn ht ha hR0 mean)
    (A).liftedData (A).controls (A).bounds

noncomputable def nearLanguage (right : Bool) : Language:=IntegralFramedPhysicalNear.guarded
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
  (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false)
  (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false)
  (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false) right

theorem near_decider (right : Bool) : SpaceDecider (nearLanguage hn ht ha hR0 right):=
  IntegralFramedPhysicalNear.guarded_decider (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false) (positive hn ht ha hR0 false)
    (A).parameters (A).nodes (A).factor (A).seed (metadata hn ht ha hR0)
    (IntegralMixedPhysicalTraceCutTest.probeControls hn ht ha (radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.probeBounds hn ht ha (radius_binary hR0) false)
    (A).liftedData (A).controls (A).bounds T hT hr
    (parent_FP hn ht ha hR0 false) (terminal_FP hn ht ha hR0 false)
    (centerIndex_binary hn ht ha hR0 right) (pointIndex_binary hn ht ha hR0 false false)
    (sampler_access hn ht ha hR0 false)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false) right

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
