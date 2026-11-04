/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendLatestCompanion
/-! # The accepted appended vertex reads the chosen child point -/
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
  IntegralMixedRoadmapAtomic.initial preparedRoot IntegralMixedPhysicalPointCompanionScan.geometricPoint

private theorem geometric_point_heq (c d u v : List Bool) (hc : c=d) (hw : u=v)
    (hu : SquareSampleCompleteVertices.Valid S c u) (hv : SquareSampleCompleteVertices.Valid S d v)
    (a b : ℕ) (hab : a=b) :
    HEq (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c u hu a)
      (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false d v hv b):=by
  subst d
  subst v
  subst b
  rfl

theorem point_of_fresh_readback (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0)
    (hNew : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet (D old) old e w)) :
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 (packet (D old) old e w) hNew) p:=by
  let q:=packet (D old) old e []
  let a:=IntegralMixedRoadmapAtomic.anchor (D old) (N old) q
  have HA0 : beginBirth hn ht ha hR0 old≤a:=by
    dsimp only [a,q]
    rw [child_anchor]
    omega
  have HA1 : a<finishBirth hn ht ha hR0 old e:=by
    dsimp only [a,q]
    rw [child_anchor,finish_eq]
    omega
  have HP:=hr.physical a HA0 (HA1.trans_le (finish_le_full hn ht ha hR0 old hv hd e he))
  rw [ite_eq_left HA1] at HP
  have HB : IntegralMixedRoadmapAtomic.anchor (D (packet (D old) old e w)) (N (packet (D old) old e w))
      (packet (D old) old e w)=a:=by
    dsimp only [a,q]
    simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.anchor,IntegralMixedRoadmapAtomic.endBirth,
      IntegralMixedRoadmapAtomic.free,payload_packet,depth_packet]
  have HG:=geometric_point_heq hn ht ha hR0 _ _ _ _ (packet_context hn ht ha hR0 old e w)
    (word_packet (D old) old e w) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 _ hNew) hw _ a HB
  exact HG.trans (heq_of_eq HP)

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
