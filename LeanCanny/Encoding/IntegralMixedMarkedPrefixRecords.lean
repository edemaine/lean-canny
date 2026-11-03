/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
public import LeanCanny.Algebra.IntegralMixedStaticRecordPrefix
/-! # Actual marked causal records agree before a changed original probe -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixRecords
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate original number)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerSource.source
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0)

theorem source_cap (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient root+1) (Q root).degree≤2^(P).width root :=by
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
  exact IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha root
noncomputable def polynomial (root : List Bool) (i : ℕ) :=
  (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).polynomial (pair root (BinaryNatCode.encode i))
theorem polynomial_nonzero (root : List Bool) (i : ℕ) : polynomial hn ht ha (R0:=R0) root i≠0 :=
  IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha (radius R0) _
theorem polynomial_degree (root : List Bool) (i : ℕ) :
    (polynomial hn ht ha (R0:=R0) root i).natDegree≤2^(P).width root :=
  ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).degree_bound _).trans
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha (radius R0) root i)

noncomputable def records (root : List Bool) : List (Record ((P).ambient root) ((P).width root)) :=
  IntegralMixedStaticRecordPrefix.records (Q root) (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (source_cap hn ht ha hR0 root) (number n root+8) (IntegralMixedCausalRecordPlanBits.count root)
    (polynomial hn ht ha (R0:=R0) root) (polynomial_nonzero hn ht ha (R0:=R0) root) (polynomial_degree hn ht ha hR0 root)
    (IntegralMixedCausalRecordPlanBits.code root)

theorem length (root : List Bool) : (records hn ht ha hR0 root).length=
    IntegralMixedCausalRecordPlanBits.count root+(number n root+8) :=
  IntegralMixedStaticRecordPrefix.records_length _ _ _ _ _ _ _ _ _
theorem room (root : List Bool) : (records hn ht ha hR0 root).length≤(P).cap root+2 :=by
  rw [length]
  change _≤number n root+8+IntegralMixedCausalRecordPlanBits.count root+2+2
  omega

theorem rules (root : List Bool) : (D).rules root=
    IntegralMixedCausalPlanBits.commands (IntegralMixedFramedHistoryFamilyBits.initial P D root)
      (records hn ht ha hR0 root) (room hn ht ha hR0 root) :=rfl

theorem source_heq (cL cR : List Bool) (hc : candidate cL=candidate cR) :HEq (Q cL) (Q cR) :=
  (heq_of_eq (IntegralMixedOriginalRegularSource.spatial_source n t R0 cL)).trans
    ((IntegralMixedOriginalRegularSource.source_congr n t R0 _ _
      (IntegralMixedMarkedPreludeCongruence.original_eq cL cR hc)).trans
        (heq_of_eq (IntegralMixedOriginalRegularSource.spatial_source n t R0 cR)).symm)

private theorem base_heq {a b S T B C : ℕ} (QL : SpatialSource a) (QR : SpatialSource b)
    (hL : PurePowerReductionBounds.dimension (a+1) QL.degree≤2^B)
    (hR : PurePowerReductionBounds.dimension (b+1) QR.degree≤2^C)
    (en : a=b) (eS : S=T) (eB : B=C) (eQ : HEq QL QR) :
    HEq (IntegralMixedHistory.base QL (IntegralHistorySampler.base S (2^B)) hL)
      (IntegralMixedHistory.base QR (IntegralHistorySampler.base T (2^C)) hR) :=by
  subst b
  subst T
  subst C
  cases eq_of_heq eQ
  rfl

theorem initial_heq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR) :
    HEq (IntegralMixedFramedHistoryFamilyBits.initial P D cL) (IntegralMixedFramedHistoryFamilyBits.initial P D cR) :=by
  change HEq (IntegralMixedHistory.base (Q cL) (IntegralHistorySampler.base ((P).cap cL+1) (2^(P).width cL)) _)
    (IntegralMixedHistory.base (Q cR) (IntegralHistorySampler.base ((P).cap cR+1) (2^(P).width cR)) _)
  exact base_heq _ _ _ _ (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc)
    (congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 cL cR hc hcount))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc) (source_heq (n:=n) (t:=t) (R0:=R0) cL cR hc)

theorem prefix_heq (cL cR : List Bool) (hc : candidate cL=candidate cR)
    (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count cL)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code cL i=IntegralMixedCausalRecordPlanBits.code cR i) :
    HEq ((records hn ht ha hR0 cL).reverse.take (number n cL+8+j))
      ((records hn ht ha hR0 cR).reverse.take (number n cR+8+j)) :=by
  unfold records
  apply IntegralMixedStaticRecordPrefix.prefix_heq
  · exact hj
  · exact IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 cL cR hc
  · exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 cL cR hc
  · exact congrArg (·+8) (IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc)
  · exact hcount
  · exact source_heq (n:=n) (t:=t) (R0:=R0) cL cR hc
  · exact IntegralMixedMarkedPreludeCongruence.polynomial hn ht ha R0 cL cR hc
  · exact hcode
end LeanCanny.Encoding.IntegralMixedMarkedPrefixRecords
