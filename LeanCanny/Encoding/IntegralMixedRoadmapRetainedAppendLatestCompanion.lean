/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChildHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPacket
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendScans
/-! # Actual new child columns imply the complete latest companion guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot

theorem latest_companion_of_fresh_readback (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0) :
    IntegralMixedRoadmapAtomic.companionQuery (D (packet (D old) old e w)) (N (packet (D old) old e w))
      (packet (D old) old e w)∈IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false:=by
  let q:=packet (D old) old e []
  let a:=IntegralMixedRoadmapAtomic.anchor (D old) (N old) q
  let f:=IntegralMixedRoadmapAtomic.first (D old) (N old) q
  let k:=IntegralMixedRoadmapAtomic.free (D old) q
  have HA0 : beginBirth hn ht ha hR0 old≤a:=by
    dsimp only [a,q]
    rw [child_anchor]
    omega
  have HA1 : a<finishBirth hn ht ha hR0 old e:=by
    dsimp only [a,q]
    rw [child_anchor,finish_eq]
    omega
  have HF : beginBirth hn ht ha hR0 old≤f:=by
    dsimp only [f,IntegralMixedRoadmapAtomic.first]
    change beginBirth hn ht ha hR0 old≤a+1
    omega
  have HFK : f+k≤finishBirth hn ht ha hR0 old e:=by
    have HDepth : IntegralMixedRoadmapAtomic.depth q≤D old:=by
      dsimp only [q]
      rw [depth_packet]
      omega
    have HEnd:=IntegralMixedRoadmapAtomic.block_end (D old) (N old) q HDepth
    exact HEnd.le
  have HComp:=companion_of_fresh_readback hn ht ha hR0 old e w hw p p0 hr a f k HA0 HA1 HF HFK
    (finish_le_full hn ht ha hR0 old hv hd e he) (child_anchor_active hn ht ha hR0 old hv hd e he)
    (fun j hj=>child_capture_active hn ht ha hR0 old hv hd e he j hj)
  exact Eq.mpr (congrArg (fun z=>z∈IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false)
    (packet_companion_query hn ht ha hR0 old e w)) HComp

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
