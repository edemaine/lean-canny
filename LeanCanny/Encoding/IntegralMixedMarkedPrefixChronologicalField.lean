/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
/-! # Every actual prefix bank value is its own chronological full-word field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixChronologicalField
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

theorem value (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid SAMP (IntegralMixedMarkedPrefixFieldReadback.context root) w)
    (j :ℕ) (hj :j≤IntegralMixedCausalRecordPlanBits.count root) (k :ℕ) (hk :k<number n root+8+j) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj).point
      (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw) k=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedMarkedPrefixFieldReadback.context root) w hw (number n root+8+j-1-k):=by
  have HP:=IntegralMixedMarkedPrefixPoint.value hn ht ha hR0 root w hw j hj k hk
  have HC:IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedMarkedPrefixFieldReadback.context root)=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair]
  have HFit:number n root+8+j≤IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    omega
  have HE:IntegralMixedPhysicalFieldEquality.newest
      (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
        (IntegralMixedMarkedPrefixFieldReadback.context root)) (number n root+8+j-1-k)=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-(number n root+8+j)+k:=by
    rw [HC]
    unfold IntegralMixedPhysicalFieldEquality.newest
    rw [min_eq_left (by omega)]
    omega
  unfold IntegralMixedPhysicalFieldEquality.point
  rw [HE]
  exact HP

end LeanCanny.Encoding.IntegralMixedMarkedPrefixChronologicalField
