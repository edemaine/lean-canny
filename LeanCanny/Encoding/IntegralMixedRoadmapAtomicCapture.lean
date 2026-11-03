/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicOccurrence
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicCaptureRecords
/-! # Every latest capture selects its exact chronological physical coordinate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B

theorem first_ge_initial (q :List Bool) (hv :Valid hn ht ha hR0 q) :
    initial hn ht ha hR0 q<first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q:=by
  have HE:=latest_block_end hn ht ha hR0 q hv
  have HH :dimension hn ht ha hR0 q+2≤IntegralMixedRoadmapChain.rawStart (dimension hn ht ha hR0 q) (payload q) (depth q):=by
    unfold IntegralMixedRoadmapChain.rawStart;omega
  unfold endBirth free at HE
  omega

theorem capture_raw_fit (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-initial hn ht ha hR0 q+j<
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q):=by
  have HF:=first_ge_initial hn ht ha hR0 q hv
  have HE:=latest_block_end hn ht ha hR0 q hv
  have HH:=IntegralMixedRoadmapChain.rawStart_bound (dimension hn ht ha hR0 q) (payload q) (depth q)
    (by have HD:=depth_le hn ht ha hR0 q hv;omega)
  unfold endBirth at HE
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem capture_good (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    IntegralMixedChronologicalFrameCode.PointGood (dimension hn ht ha hR0 q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) (frozen q) (depth q)
      (dimension hn ht ha hR0 q-j):=capture_point_good (checked hn ht ha hR0 q hv) j hj

theorem capture_creating_command (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (root q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j)).command=
    .critical (IntegralMixedChronologicalFrameCode.rawData (dimension hn ht ha hR0 q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) (frozen q) (depth q)
      (dimension hn ht ha hR0 q-j) (capture_good hn ht ha hR0 q hv j hj)).rule:=by
  have HC :IntegralMixedCausalRecordPlanBits.count (root q)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension hn ht ha hR0 q):=by
    change WordListRecords.count (pairFst (pairSnd (root q)))=_
    simpa only [root,pairSnd_pair,pairFst_pair] using raw_count hn ht ha hR0 q hv
  have HN :IntegralMixedAuxiliaryMarkedIntegerSource.number n (root q)+8=initial hn ht ha hR0 q:=by
    rw [initial_eq hn ht ha hR0 q]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,original]
  have HW :IntegralMixedCausalRecordPlanBits.code (root q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q-initial hn ht ha hR0 q+j)=
      IntegralMixedChronologicalFrameCode.code (dimension hn ht ha hR0 q) (frozen q) (depth q)
        (dimension hn ht ha hR0 q-j):=by
    simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
      root,pairFst_pair,pairSnd_pair] using latest_capture_record (checked hn ht ha hR0 q hv) j hj
  exact IntegralMixedMarkedRecordReceipt.critical_at hn ht ha hR0 (root q) _ _
    (by rw [HC];exact capture_raw_fit hn ht ha hR0 q hv j hj)
    (by rw [HN];have HH:=first_ge_initial hn ht ha hR0 q hv;omega) _ _ _
    (capture_good hn ht ha hR0 q hv j hj) HW

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem native_capture_good (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (pairFst ((B).key (context q))))
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) (frozen q) (depth q)
      (dimension hn ht ha hR0 q-j):=by
  rw [native_dimension hn ht ha hR0 q]
  exact capture_good hn ht ha hR0 q hv j hj

theorem native_capture_command (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    (IntegralMixedFramedRootPullback.instructionAt P D (pairFst ((B).key (context q)))
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient (pairFst ((B).key (context q))))
        (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j) (frozen q) (depth q)
        (dimension hn ht ha hR0 q-j) (native_capture_good hn ht ha hR0 q hv j hj)).rule:=by
  exact IntegralMixedStaticRecordLookup.critical_root_transport P D (root q) _
    (context_root hn ht ha hR0 q).symm _ _ _ _ (capture_good hn ht ha hR0 q hv j hj)
    (native_capture_good hn ht ha hR0 q hv j hj) (capture_creating_command hn ht ha hR0 q hv j hj)

theorem capture_selected (q :List Bool) (hv :Valid hn ht ha hR0 q) (j :ℕ)
    (hj :j<free (dimension hn ht ha hR0 q) q) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (context q)
      (first (dimension hn ht ha hR0 q) (initial hn ht ha hR0 q) q+j)=dimension hn ht ha hR0 q-j:=
  IntegralMixedPhysicalPointCompanionScan.selected_of_frame hn ht ha (radius_binary hR0) false _ _ _ _ _
    (native_capture_good hn ht ha hR0 q hv j hj) (native_capture_command hn ht ha hR0 q hv j hj)

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic
