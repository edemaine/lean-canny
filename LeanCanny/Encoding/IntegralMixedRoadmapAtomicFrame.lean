/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
public import LeanCanny.Encoding.IntegralMixedMarkedRecordReceipt
/-! # The current atomic frame is the literal latest creating record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] dimension initial width sourceCap scalarBudget root context payload candidate word

theorem own_frame_good (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedChronologicalFrameCode.Good (dimension hn ht ha hR0 q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1) (frozen q) :=by
  have HD:=depth_le hn ht ha hR0 q hv
  have HE:=latest_block_end hn ht ha hR0 q hv
  have HF :0<free (dimension hn ht ha hR0 q) q:=by unfold free;omega
  have HA :anchor (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q≤
      endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1 :=by unfold first at HE;omega
  cases Hdepth :depth q with
  | zero=>
    have HW :frozen q=[]:=by change IntegralMixedRoadmapChain.frozen (payload q) (depth q)=[];rw [Hdepth];rfl
    rw [HW]
    exact (IntegralMixedRoadmapChain.seed_point_good _ _ 0 (by omega)).1
  | succ i=>
    have HI :i<IntegralMixedRoadmapChain.depth (payload q):=by change i<depth q;omega
    have HC:=IntegralMixedRoadmapLevel.child_frame_good
      (IntegralMixedRoadmapChain.level_checked (checked hn ht ha hR0 q hv) i HI).1
    rw [IntegralMixedRoadmapChain.level_frozen] at HC
    have HW :IntegralMixedRoadmapChain.frozen (payload q) (i+1)=frozen q:=by unfold frozen;rw [Hdepth]
    rw [HW] at HC
    exact IntegralMixedRoadmapLevel.frame_mono HC
      ((child_anchor _ _ q i Hdepth (by omega)).symm.trans_le HA)

theorem own_point_good (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedChronologicalFrameCode.PointGood (dimension hn ht ha hR0 q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1) (frozen q) (depth q) (depth q) :=by
  have HD:=depth_le hn ht ha hR0 q hv
  refine ⟨own_frame_good hn ht ha hR0 q hv,?_,by omega,?_,by omega⟩ <;> rw [frozen_count]

theorem own_raw_fit (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1<
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q) :=by
  have HH:=IntegralMixedRoadmapChain.rawStart_bound (dimension hn ht ha hR0 q) (payload q) (depth q)
    (by have HD:=depth_le hn ht ha hR0 q hv;omega)
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

attribute [local semireducible] dimension

theorem own_creating_command (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan (root q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)).command=
    .critical (IntegralMixedChronologicalFrameCode.rawData (dimension hn ht ha hR0 q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1) (frozen q) (depth q) (depth q)
      (own_point_good hn ht ha hR0 q hv)).rule :=by
  have HC :IntegralMixedCausalRecordPlanBits.count (root q)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q):=by
    change WordListRecords.count (pairFst (pairSnd (root q)))=_
    simpa only [root,pairSnd_pair,pairFst_pair] using raw_count hn ht ha hR0 q hv
  have HW :IntegralMixedCausalRecordPlanBits.code (root q)
      (IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1)=
      IntegralMixedChronologicalFrameCode.code (dimension hn ht ha hR0 q) (frozen q) (depth q) (depth q):=by
    simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
      root,pairFst_pair,pairSnd_pair] using own_height_record hn ht ha hR0 q hv
  have HN :IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8=initial hn ht ha hR0 q:=by
    rw [initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,original]
  have HP :0<IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q):=by
    unfold IntegralMixedRoadmapChain.rawStart;omega
  have HE :IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8+
      (IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1)=
      endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1:=by
    unfold endBirth;rw [HN];omega
  exact IntegralMixedMarkedRecordReceipt.critical_at hn ht ha hR0 (root q)
    (IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1)
    (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)
    (by rw [HC];exact own_raw_fit hn ht ha hR0 q hv) HE.symm (frozen q) (depth q) (depth q)
    (own_point_good hn ht ha hR0 q hv) HW

theorem own_creating_source (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan (root q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)).source=
      IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (IntegralMixedOriginalRegularSource.radius R0) (root q) :=by
  have HC :IntegralMixedCausalRecordPlanBits.count (root q)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q):=by
    change WordListRecords.count (pairFst (pairSnd (root q)))=_
    simpa only [root,pairSnd_pair,pairFst_pair] using raw_count hn ht ha hR0 q hv
  have HN :IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8=initial hn ht ha hR0 q:=by
    rw [initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,original]
  have HP :0<IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q):=by
    unfold IntegralMixedRoadmapChain.rawStart;omega
  exact IntegralMixedMarkedRecordReceipt.source_at hn ht ha hR0 (root q)
    (IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q)-1)
    (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)
    (by rw [HC];exact own_raw_fit hn ht ha hR0 q hv) (by unfold endBirth;rw [HN];omega)

theorem own_creating_source_heq (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    HEq (IntegralMixedFramedRootPullback.instructionAt
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).plan (root q)
      (endBirth (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-1)).source
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (IntegralMixedOriginalRegularSource.radius R0) (root q)) :=
  heq_of_eq (own_creating_source hn ht ha hR0 q hv)

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
