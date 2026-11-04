/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCompanions
/-! # The accepted proper append reads exactly its constructed child point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

private theorem geometric_point_heq (c d u v :List Bool) (hc :c=d) (hw :u=v)
    (hu :SquareSampleCompleteVertices.Valid SAMP c u) (hv :SquareSampleCompleteVertices.Valid SAMP d v)
    (a b :ℕ) (hab :a=b):
    HEq (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false c u hu a)
      (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false d v hv b):=by
  subst d
  subst v
  subst b
  rfl

private theorem cast_point_heq {a b :ℕ} (h:a=b) (p :Fin b→ℝ):
    HEq (fun i :Fin a=>p (Fin.cast h i)) p:=by
  subst b
  apply heq_of_eq
  funext i
  apply congrArg p
  apply Fin.ext
  rfl

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "q0"=>packet D old R.leftSpec R.rightSpec side []
local notation "CTX"=>pair r []
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0
local notation "anchor"=>IntegralMixedRoadmapAtomic.anchor
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalPointCompanionScan.geometricPoint preparedRoot
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

/-- Acceptance supplies only the proof-indexed public point. Its actual value
comes from W and the same physical readback N, not from another sampled word. -/
theorem WordReceipt.point_eq_child {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word)):
    HEq (IntegralMixedRoadmapAtomic.point hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV) pChild:=by
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HP:=W.local_geometric_point hn ht ha hR0 old hv hd left right R side N anchor (by omega) (by omega)
  rw [ite_eq_right (by omega :¬anchor<anchor)] at HP
  have HC :IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side W.word)=CTX:=by
    simp only [IntegralMixedRoadmapAtomic.context,preparedRoot,IntegralMixedRoadmapAtomic.root,
      candidate_packet,payload_packet]
  have HB :IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (packet D old R.leftSpec R.rightSpec side W.word)=anchor:=by
    simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.anchor,
      IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.free,depth_packet,payload_packet]
  have HG:=geometric_point_heq hn ht ha hR0 _ _ _ _ HC (word_packet _ _ _ _ _ _)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 _ hV) W.valid _ anchor HB
  have HCast :HEq (nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild) pChild:=
    cast_point_heq (congrArg (·+1) (physical_dimension hn ht ha hR0 old hv hd left right R side)) pChild
  exact HG.trans ((heq_of_eq HP).trans HCast)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
