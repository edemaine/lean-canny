/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendFieldScalar
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedCompanionReadback
/-! # Both actual companion queries accept the same constructed full word -/
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
local notation "BS"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "SS"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

private theorem companion_extend_finite {a :ℕ} (p :Fin a→ℝ) (i :Fin a) :
    IntegralMixedFramedBankObservation.extend p i.val=p i:=by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

private theorem midpoint_from_extended (q :List Bool)
    (HC :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
      (IntegralMixedRoadmapAtomic.payload q)) (HD :0<IntegralMixedRoadmapAtomic.depth q)
    (ctx w :List Bool) (hctx :IntegralMixedRoadmapAtomic.context q=ctx) (hword :IntegralMixedRoadmapAtomic.word q=w)
    (hw :SquareSampleCompleteVertices.Valid SS ctx w)
    (p :Fin ((BS).parameters.ambient (pairFst ((BS).key ctx))+1)→ℝ)
    (hA :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw
      (IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q)=p)
    (hP :∀i,i<IntegralMixedRoadmapProper.captureCount (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q→
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw
        (IntegralMixedRoadmapProper.midFirst (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i)=p)
    (hF :∀i,i<IntegralMixedRoadmapProper.captureCount (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q→
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) ctx w hw
        (IntegralMixedRoadmapProper.midFirst (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i)=
      IntegralMixedFramedBankObservation.extend p
        (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ctx
          (IntegralMixedRoadmapProper.midFirst (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
            (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i))) :
    IntegralMixedRoadmapProper.Midpoint hn ht ha hR0 q:=by
  subst ctx
  subst w
  exact IntegralMixedRoadmapCheckedCompanionReadback.midpoint_of_readback hn ht ha hR0 q HC HD hw p hA hP
    (fun i hi=>(hF i hi).trans (companion_extend_finite p
      (IntegralMixedRoadmapCheckedCompanionReadback.midCaptureIndex hn ht ha hR0 q HC HD i hi)))

private theorem child_from_extended (q :List Bool)
    (HC :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
      (IntegralMixedRoadmapAtomic.payload q))
    (ctx w :List Bool) (hctx :IntegralMixedRoadmapAtomic.context q=ctx) (hword :IntegralMixedRoadmapAtomic.word q=w)
    (hw :SquareSampleCompleteVertices.Valid SS ctx w)
    (p :Fin ((BS).parameters.ambient (pairFst ((BS).key ctx))+1)→ℝ)
    (hA :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw
      (IntegralMixedRoadmapAtomic.anchor (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q)=p)
    (hP :∀i,i<IntegralMixedRoadmapAtomic.free (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q→
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw
        (IntegralMixedRoadmapAtomic.first (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i)=p)
    (hF :∀i,i<IntegralMixedRoadmapAtomic.free (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q→
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) ctx w hw
        (IntegralMixedRoadmapAtomic.first (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i)=
      IntegralMixedFramedBankObservation.extend p
        (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ctx
          (IntegralMixedRoadmapAtomic.first (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
            (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i))) :
    IntegralMixedRoadmapAtomic.companionQuery (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q∈IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false:=by
  subst ctx
  subst w
  exact IntegralMixedRoadmapCheckedCompanionReadback.child_of_readback hn ht ha hR0 q HC hw p hA hP
    (fun i hi=>(hF i hi).trans (companion_extend_finite p
      (IntegralMixedRoadmapCheckedCompanionReadback.childCaptureIndex hn ht ha hR0 q HC i hi)))

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "q0"=>packet D old R.leftSpec R.rightSpec side []
local notation "CTX"=>pair r []
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "K"=>List.length (R.orderedFree hk)
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0
local notation "anchor"=>IntegralMixedRoadmapAtomic.anchor
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side

noncomputable local instance properAppendCompanionsIndexFintype :Fintype (Index (Fin 0) oldCs):=
  indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalFieldEquality.point
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentState IntegralMixedRoadmapRetainedAppend.parentDescriptor
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private theorem companion_packet_context (w :List Bool) :
    IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side w)=CTX:=by
  simp only [IntegralMixedRoadmapAtomic.context,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet]

private theorem companion_checked (w :List Bool) :
    IntegralMixedRoadmapChain.Checked
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.payload (packet D old R.leftSpec R.rightSpec side w)):=by
  rw [dimension_packet,initial_packet,payload_packet]
  simpa only [IntegralMixedRoadmapAtomic.scalarBudget,original_packet] using
    pair_checked hn ht ha hR0 old hv hd left right R side w

private theorem companion_mid_clock (w :List Bool) :
    IntegralMixedRoadmapProper.midBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=mid:=by
  simp only [dimension_packet,initial_packet,IntegralMixedRoadmapProper.midBirth,
    IntegralMixedRoadmapProper.baseBirth,IntegralMixedRoadmapProper.levelIndex,depth_packet,payload_packet]

private theorem companion_mid_first (w :List Bool) :
    IntegralMixedRoadmapProper.midFirst
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=mid+1:=by
  exact congrArg (·+1) (companion_mid_clock hn ht ha hR0 old hv hd left right R side w)

private theorem companion_mid_count (w :List Bool) :
    IntegralMixedRoadmapProper.captureCount
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapProper.captureCount (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) q0:=by
  simp only [dimension_packet,IntegralMixedRoadmapProper.captureCount,IntegralMixedRoadmapProper.levelIndex,depth_packet]

private theorem companion_child_clock (w :List Bool) :
    IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=anchor:=by
  simp only [dimension_packet,initial_packet,IntegralMixedRoadmapAtomic.anchor,
    IntegralMixedRoadmapAtomic.endBirth,IntegralMixedRoadmapAtomic.free,depth_packet,payload_packet]

private theorem companion_child_first (w :List Bool) :
    IntegralMixedRoadmapAtomic.first
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=anchor+1:=by
  exact congrArg (·+1) (companion_child_clock hn ht ha hR0 old hv hd left right R side w)

private theorem companion_child_count (w :List Bool) :
    IntegralMixedRoadmapAtomic.free
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapAtomic.free (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) q0:=by
  simp only [dimension_packet,IntegralMixedRoadmapAtomic.free,depth_packet]

private theorem extend_cast {a b :ℕ} (h :a=b) (p :Fin b→ℝ) (k :ℕ) :
    IntegralMixedFramedBankObservation.extend (fun i :Fin a=>p (Fin.cast h i)) k=
      IntegralMixedFramedBankObservation.extend p k:=by
  subst b
  have HE :(fun i :Fin a=>p (Fin.cast (rfl :a=a) i))=p:=by
    funext i
    apply congrArg p
    apply Fin.ext
    rfl
  rw [HE]

private theorem companion_extend_native (p :Fin ((P).ambient c+1)→ℝ) (coord :ℕ) :
    IntegralMixedFramedBankObservation.extend p coord=
      IntegralMixedFramedBankObservation.extend (nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side p) coord:=
  (extend_cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old hv hd left right R side)) p coord).symm

theorem WordReceipt.local_scalar_point {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finish) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=
      IntegralMixedFramedBankObservation.extend (if b<anchor then pMID else pChild)
        (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX b):=by
  have HV:=physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N
  have H:=W.scalar_before_finish hn ht ha hR0 old hv hd left right R side pMID pChild HV b hb0 hb1
  simpa only [companion_packet_context hn ht ha hR0 old hv hd left right R side []] using H

theorem WordReceipt.local_geometric_point {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finish) :
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b=
      if b<anchor then nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pMID
      else nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild:=by
  have HF:=full_birth hn ht ha hR0 old hv hd left right R side
  have H:=physical_of_word_receipt hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b hb0 (by omega)
  simpa only [ite_eq_left hb1] using H

theorem WordReceipt.midpoint_companion {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild) :
    IntegralMixedRoadmapProper.Midpoint hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word):=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  have HC:=companion_checked hn ht ha hR0 old hv hd left right R side W.word
  have HD:0<IntegralMixedRoadmapAtomic.depth q:=by rw [depth_packet];omega
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HK:=capture_count hn ht ha hR0 old hv hd left right R side
  apply midpoint_from_extended hn ht ha hR0 q HC HD CTX W.word
    (companion_packet_context hn ht ha hR0 old hv hd left right R side W.word)
    (word_packet _ _ _ _ _ _) W.valid
    (nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pMID)
  · dsimp only [q]
    rw [companion_mid_clock hn ht ha hR0 old hv hd left right R side W.word]
    simpa only [ite_eq_left (by omega :mid<anchor)] using
      W.local_geometric_point hn ht ha hR0 old hv hd left right R side N mid (by omega) (by omega)
  · intro i hi
    have HI:i<K:=hi.trans_eq ((companion_mid_count hn ht ha hR0 old hv hd left right R side W.word).trans HK)
    dsimp only [q]
    rw [companion_mid_first hn ht ha hR0 old hv hd left right R side W.word]
    simpa only [ite_eq_left (by omega :mid+1+i<anchor)] using
      W.local_geometric_point hn ht ha hR0 old hv hd left right R side N (mid+1+i) (by omega) (by omega)
  · intro i hi
    have HI:i<K:=hi.trans_eq ((companion_mid_count hn ht ha hR0 old hv hd left right R side W.word).trans HK)
    dsimp only [q]
    rw [companion_mid_first hn ht ha hR0 old hv hd left right R side W.word]
    have HS:=W.local_scalar_point hn ht ha hR0 old hv hd left right R side N (mid+1+i) (by omega) (by omega)
    rw [ite_eq_left (by omega :mid+1+i<anchor)] at HS
    exact HS.trans (companion_extend_native hn ht ha hR0 old hv hd left right R side pMID _)

theorem WordReceipt.child_companion {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild) :
    IntegralMixedRoadmapAtomic.companionQuery
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
      (packet D old R.leftSpec R.rightSpec side W.word)∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false:=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  have HC:=companion_checked hn ht ha hR0 old hv hd left right R side W.word
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HK:=child_free hn ht ha hR0 old hv hd left right R side
  apply child_from_extended hn ht ha hR0 q HC CTX W.word
    (companion_packet_context hn ht ha hR0 old hv hd left right R side W.word)
    (word_packet _ _ _ _ _ _) W.valid
    (nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild)
  · dsimp only [q]
    rw [companion_child_clock hn ht ha hR0 old hv hd left right R side W.word]
    simpa only [ite_eq_right (by omega :¬anchor<anchor)] using
      W.local_geometric_point hn ht ha hR0 old hv hd left right R side N anchor (by omega) (by omega)
  · intro i hi
    have HI:i<K:=hi.trans_eq ((companion_child_count hn ht ha hR0 old hv hd left right R side W.word).trans HK)
    dsimp only [q]
    rw [companion_child_first hn ht ha hR0 old hv hd left right R side W.word]
    simpa only [ite_eq_right (by omega :¬anchor+1+i<anchor)] using
      W.local_geometric_point hn ht ha hR0 old hv hd left right R side N (anchor+1+i) (by omega) (by omega)
  · intro i hi
    have HI:i<K:=hi.trans_eq ((companion_child_count hn ht ha hR0 old hv hd left right R side W.word).trans HK)
    dsimp only [q]
    rw [companion_child_first hn ht ha hR0 old hv hd left right R side W.word]
    have HS:=W.local_scalar_point hn ht ha hR0 old hv hd left right R side N (anchor+1+i) (by omega) (by omega)
    rw [ite_eq_right (by omega :¬anchor+1+i<anchor)] at HS
    exact HS.trans (companion_extend_native hn ht ha hR0 old hv hd left right R side pChild _)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
