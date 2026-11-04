/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalFields
/-! # Original coordinate fields are the constructed MID and child coordinates -/
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

private theorem original_capture_at_context (q ctx w :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hw :SquareSampleCompleteVertices.Valid SAMP ctx w)
    (hc :IntegralMixedRoadmapAtomic.context q=ctx) (he :IntegralMixedRoadmapAtomic.word q=w) (i :ℕ):
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) ctx w hw i:=by
  subst ctx
  subst w
  rfl

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "q0"=>packet D old R.leftSpec R.rightSpec side []
local notation "CTX"=>pair r []
local notation "K"=>List.length (R.orderedFree hk)
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapLocalFrame.field IntegralMixedPhysicalFieldEquality.point
  NativePair.orderedFree

private theorem capture_dimension :(P).ambient c=D:=
  IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e

private theorem localCapture_count :K=D-IntegralMixedRoadmapAtomic.depth old:=by
  have H:=R.orderedFree_length hk
  have HD:=capture_dimension hn ht ha hR0 old
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  have HNUM :((P).ambient c)+1-((d).labels.length+1)=D-IntegralMixedRoadmapAtomic.depth old:=by omega
  exact H.trans HNUM

private theorem capture_context (w :List Bool):
    IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side w)=CTX:=by
  simp only [IntegralMixedRoadmapAtomic.context,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet,preparedRoot]

private theorem capture_mid_clock (w :List Bool):
    IntegralMixedRoadmapProper.midBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=mid:=by
  simp only [dimension_packet,initial_packet,IntegralMixedRoadmapProper.midBirth,
    IntegralMixedRoadmapProper.baseBirth,IntegralMixedRoadmapProper.levelIndex,depth_packet,payload_packet]

private theorem capture_child_clock (w :List Bool):
    IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=mid+1+K:=by
  have HC :IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=IntegralMixedRoadmapAtomic.anchor
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0:=by
    simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.anchor,
      IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.free,depth_packet,payload_packet]
  exact HC.trans (child_anchor hn ht ha hR0 old hv hd left right R side)

/-- Both actual original-word capture fields read the given coordinate of the
two constructed physical points. The points are not identified with each other. -/
theorem WordReceipt.original_capture_fields {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D):
    ∃ij :Fin ((P).ambient c+1),ij.val=j ∧
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV
        (IntegralMixedRoadmapProper.midProducer
          (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
          (packet D old R.leftSpec R.rightSpec side W.word) j)=pMID ij ∧
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word) hV
        (IntegralMixedRoadmapProper.childProducer
          (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
          (packet D old R.leftSpec R.rightSpec side W.word) j)=pChild ij:=by
  have HK:=localCapture_count hn ht ha hR0 old hv hd left right R
  have HD:=capture_dimension hn ht ha hR0 old
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  let k :Fin K:=⟨j-(IntegralMixedRoadmapAtomic.depth old+1),by omega⟩
  let ij :Fin ((P).ambient c+1):=⟨j,by omega⟩
  have HE :((R.orderedFree hk).get k).val=ij:=by
    apply Fin.ext
    have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
    exact (R.orderedFree_get hk k).trans (by dsimp only [k,ij];omega)
  have HB :IntegralMixedRoadmapProper.midProducer
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (packet D old R.leftSpec R.rightSpec side W.word) j=finish-1-(K+1+k.val):=by
    unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst
    rw [capture_mid_clock hn ht ha hR0 old hv hd left right R side W.word]
    simp only [dimension_packet]
    have HFF:=HF
    simp only [dimension_packet] at HFF
    dsimp only [k]
    omega
  have HC :IntegralMixedRoadmapProper.childProducer
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (packet D old R.leftSpec R.rightSpec side W.word) j=finish-1-k.val:=by
    unfold IntegralMixedRoadmapProper.childProducer IntegralMixedRoadmapAtomic.first
    rw [capture_child_clock hn ht ha hR0 old hv hd left right R side W.word]
    simp only [dimension_packet]
    have HFF:=HF
    simp only [dimension_packet] at HFF
    dsimp only [k]
    omega
  have HV:=physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N
  have HM:=W.midpoint_capture_field hn ht ha hR0 old hv hd left right R side pMID pChild HV k
  have HChild:=W.child_capture_field hn ht ha hR0 old hv hd left right R side pMID pChild HV k
  refine ⟨ij,rfl,?_,?_⟩
  · exact (original_capture_at_context hn ht ha hR0 _ _ _ hV W.valid
      (capture_context hn ht ha hR0 old hv hd left right R side W.word) (word_packet _ _ _ _ _ _) _).trans
      ((congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid) HB).trans
        (HM.trans (congrArg pMID HE)))
  · exact (original_capture_at_context hn ht ha hR0 _ _ _ hV W.valid
      (capture_context hn ht ha hR0 old hv hd left right R side W.word) (word_packet _ _ _ _ _ _) _).trans
      ((congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid) HC).trans
        (HChild.trans (congrArg pChild HE)))

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
