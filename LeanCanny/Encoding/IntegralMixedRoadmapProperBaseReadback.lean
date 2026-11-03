/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBase

/-! # Latest midpoint guards read one actual powered physical point

All companion columns and selected scalars use the same original full word.
These conclusions are derived from accepted native guards, not an input
point-equality or interpreting-hom oracle.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedPhysicalPointCompanionScan (Active geometricPoint retained selected selected_lt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapAtomic.context
local notation "word"=>IntegralMixedRoadmapAtomic.word
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.native
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedFramedHistoryFamilyBits.family geometricPoint retained selected

noncomputable def MidCapture (q : List Bool) (hv : SquareSampleCompleteVertices.Valid S (ctx q) (word q)) : Prop:=
  ∀j<captureCount (D q) q,
    ∃hb : Active hn ht ha (radius_binary hR0) false (ctx q) (midFirst (D q) (I q) q+j),
      geometricPoint hn ht ha (radius_binary hR0) false (ctx q) (word q) hv (midFirst (D q) (I q) q+j)=
        geometricPoint hn ht ha (radius_binary hR0) false (ctx q) (word q) hv (midBirth (D q) (I q) q) ∧
      retained hn ht ha (radius_binary hR0) false (ctx q) (word q) hv (midFirst (D q) (I q) q+j) hb=
        geometricPoint hn ht ha (radius_binary hR0) false (ctx q) (word q) hv (midBirth (D q) (I q) q)
          ⟨selected hn ht ha (radius_binary hR0) false (ctx q) (midFirst (D q) (I q) q+j),
            selected_lt hn ht ha (radius_binary hR0) false (ctx q) (midFirst (D q) (I q) q+j) hb⟩

theorem midpoint_sound (q : List Bool) (H : Midpoint hn ht ha hR0 q) :
    ∃hv : SquareSampleCompleteVertices.Valid S (ctx q) (word q),
      Active hn ht ha (radius_binary hR0) false (ctx q) (midBirth (D q) (I q) q) ∧
        MidCapture hn ht ha hR0 q hv :=by
  have HV : SquareSampleCompleteVertices.Valid S (ctx q) (word q):=by
    simpa only [Midpoint,midCompanions,IntegralMixedRoadmapAtomic.sampleQuery,pairFst_pair,pairSnd_pair] using H.1
  have HA:=H.2.1.2.1
  have HA' : Active hn ht ha (radius_binary hR0) false (ctx q) (midBirth (D q) (I q) q):=by
    simpa only [Active,IntegralMixedPhysicalPointCompanionScan.anchorQuery,
      IntegralMixedPhysicalPointCompanionScan.anchor,midCompanions,IntegralMixedRoadmapAtomic.sampleQuery,
      IntegralMixedPhysicalPointCompanionScan.descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using HA
  refine ⟨HV,HA',?_⟩
  exact (IntegralMixedPhysicalPointCompanionScan.holds_iff_points hn ht ha (radius_binary hR0) false
    (ctx q) (word q) HV (midBirth (D q) (I q) q) (midFirst (D q) (I q) q) (captureCount (D q) q) HA').mp H.2.2

theorem base_midpoint_sound (q : List Bool) (H : Base hn ht ha hR0 q) :
    ∃hv : SquareSampleCompleteVertices.Valid S (ctx q) (word q),
      Active hn ht ha (radius_binary hR0) false (ctx q) (midBirth (D q) (I q) q) ∧
        MidCapture hn ht ha hR0 q hv :=midpoint_sound hn ht ha hR0 q H.2.2.1

end LeanCanny.Encoding.IntegralMixedRoadmapProper
