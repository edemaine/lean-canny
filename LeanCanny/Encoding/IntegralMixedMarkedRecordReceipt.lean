/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedStaticRecordLookup
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixRecords
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
/-! # An actual marked creating command is determined by its literal raw bytes -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedRecordReceipt
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)

theorem critical (root :List Bool) (i :ℕ) (hi :i<IntegralMixedCausalRecordPlanBits.count root)
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient root) (number n root+8+i) labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code root i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient root) labels g j) :
    (IntegralMixedFramedRootPullback.instructionAt P D root (number n root+8+i)).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient root) (number n root+8+i) labels g j hg).rule :=by
  have HR :IntegralMixedCausalRecordPlanBits.count root+(number n root+8)≤(P).cap root+1+1 :=by
    have HH:=IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root
    rw [IntegralMixedMarkedPrefixRecords.length] at HH
    exact HH
  unfold IntegralMixedFramedRootPullback.instructionAt
  rw [IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root]
  unfold IntegralMixedMarkedPrefixRecords.records
  exact IntegralMixedStaticRecordLookup.critical_receipt
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root)
    (number n root+8) (IntegralMixedCausalRecordPlanBits.count root)
    (IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root)
    (IntegralMixedCausalRecordPlanBits.code root) (initial P D root) HR (defaultInstruction P D root)
    i hi labels g j hg hw

theorem critical_at (root :List Bool) (i birth :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count root) (hb :birth=number n root+8+i)
    (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient root) birth labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code root i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient root) labels g j) :
    (IntegralMixedFramedRootPullback.instructionAt P D root birth).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData ((P).ambient root) birth labels g j hg).rule :=by
  subst birth
  exact critical hn ht ha hR0 root i hi labels g j hg hw

theorem source_at (root :List Bool) (i birth :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count root) (hb :birth=number n root+8+i) :
    (IntegralMixedFramedRootPullback.instructionAt P D root birth).source=
      IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root :=by
  subst birth
  have HR :IntegralMixedCausalRecordPlanBits.count root+(number n root+8)≤(P).cap root+1+1:=by
    have HH:=IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 root
    rw [IntegralMixedMarkedPrefixRecords.length] at HH
    exact HH
  unfold IntegralMixedFramedRootPullback.instructionAt
  rw [IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root]
  unfold IntegralMixedMarkedPrefixRecords.records
  exact IntegralMixedStaticRecordLookup.source_receipt
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root)
    (number n root+8) (IntegralMixedCausalRecordPlanBits.count root)
    (IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root)
    (IntegralMixedCausalRecordPlanBits.code root) (initial P D root) HR (defaultInstruction P D root) i hi
end LeanCanny.Encoding.IntegralMixedMarkedRecordReceipt

namespace LeanCanny.Algebra.IntegralMixedStaticRecordLookup
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem critical_root_transport (P :Parameters) (D :Plan P) (r s :List Bool) (he :r=s)
    (b :ℕ) (labels :List Bool) (g j :ℕ)
    (HG :IntegralMixedChronologicalFrameCode.PointGood (P.ambient r) b labels g j)
    (HS :IntegralMixedChronologicalFrameCode.PointGood (P.ambient s) b labels g j)
    (hc :(IntegralMixedFramedRootPullback.instructionAt P D r b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData (P.ambient r) b labels g j HG).rule) :
    (IntegralMixedFramedRootPullback.instructionAt P D s b).command=
      .critical (IntegralMixedChronologicalFrameCode.rawData (P.ambient s) b labels g j HS).rule:=by
  subst s
  exact hc
end LeanCanny.Algebra.IntegralMixedStaticRecordLookup
