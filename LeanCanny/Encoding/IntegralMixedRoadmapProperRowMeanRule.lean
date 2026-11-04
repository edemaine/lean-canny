/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowFields
public import LeanCanny.Geometry.IntegralMixedChronologicalMeanCutSpecialization
/-! # The actual mean probe changes exactly one normalized frozen row -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem raw_mean_rule {a b : ℕ} (w : List Bool) (left right g j : ℕ)
    (ho : IntegralMixedChronologicalCutCode.Good a b w g j)
    (hm : IntegralMixedChronologicalMidpointCode.Good a b w left right g j)
    (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedChronologicalMeanCutCode.rawData a b w left right g j hm).rule Q hQ=
      IntegralMixedMeanCenteredSweep.rule ((IntegralMixedChronologicalCutCode.rawData a b w g j ho).rule Q hQ)
        (IntegralMixedChronologicalMidpoint.reference ⟨left,hm.2.1⟩)
        (IntegralMixedChronologicalMidpoint.reference ⟨right,hm.2.2.1⟩) :=by
  simpa only [IntegralMixedChronologicalMeanCutCode.rawData,IntegralMixedChronologicalCutCode.rawData] using
    IntegralMixedChronologicalMeanCut.data_rule (IntegralMixedChronologicalFrameCode.descriptor a b w hm.1)
      (IntegralMixedChronologicalMidpointCode.raw_fit a b w left right g j hm)
      ⟨left,hm.2.1⟩ ⟨right,hm.2.2.1⟩ ⟨g,hm.2.2.2.2.1⟩ ⟨j,hm.2.2.2.2.2.2⟩
      (IntegralMixedChronologicalMidpointCode.raw_free_g a b w left right g j hm)
      (IntegralMixedChronologicalMidpointCode.raw_free_j a b w left right g j hm) Q hQ

private theorem raw_mean_rule_heq {a b m l : ℕ} (en : a=b) (em : m=l)
    (w : List Bool) (left right g j : ℕ)
    (ho : IntegralMixedChronologicalCutCode.Good a m w g j)
    (hm : IntegralMixedChronologicalMidpointCode.Good b l w left right g j)
    (hleft : left<m) (hright : right<m) (Q R : ℤ) (hQ : Q≠0) (hR : R≠0) (eqr : Q=R) :
    HEq ((IntegralMixedChronologicalMeanCutCode.rawData b l w left right g j hm).rule R hR)
      (IntegralMixedMeanCenteredSweep.rule ((IntegralMixedChronologicalCutCode.rawData a m w g j ho).rule Q hQ)
        (IntegralMixedChronologicalMidpoint.reference ⟨left,hleft⟩)
        (IntegralMixedChronologicalMidpoint.reference ⟨right,hright⟩)) :=by
  cases en
  cases em
  subst R
  exact heq_of_eq (raw_mean_rule w left right g j ho hm Q hQ)

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable def meanReference (right : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    Fin (parentBirth hn ht ha hR0 false z):=
  IntegralMixedChronologicalMidpoint.reference ⟨oldProducer right z,by
    have H:=parent_good hn ht ha hR0 false z (row_count_positive hn ht ha hR0 z hv) hg
    cases right
    · exact H.2.2.1
    · exact H.2.2.2.1⟩

theorem parent_denominator_eq (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    commonDenominator ((G).state (parentKey hn ht ha hR0 false z))=
      commonDenominator ((G).state (parentKey hn ht ha hR0 true z)) :=
  congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>commonDenominator d.state)
    (parent_state_snapshot_eq_valid hn ht ha hR0 z hv)

theorem actual_mean_rule (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    HEq ((G).rule (parentKey hn ht ha hR0 true z))
      (IntegralMixedMeanCenteredSweep.rule ((G).rule (parentKey hn ht ha hR0 false z))
        (meanReference hn ht ha hR0 false z hv hg) (meanReference hn ht ha hR0 true z hv hg)) :=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  have HO:=parent_good hn ht ha hR0 false z HC hg
  have HM:=parent_good hn ht ha hR0 true z HC hg
  have EN : parentDimension hn ht ha hR0 false z=parentDimension hn ht ha hR0 true z:=
    (parentDimension_eq hn ht ha hR0 false z).trans (parentDimension_eq hn ht ha hR0 true z).symm
  have EM : parentBirth hn ht ha hR0 false z=parentBirth hn ht ha hR0 true z:=
    (parentBirth_eq hn ht ha hR0 false z HC).trans (parentBirth_eq hn ht ha hR0 true z HC).symm
  have HE:=raw_mean_rule_heq EN EM (labels z) (oldProducer false z) (oldProducer true z)
    (offset z) (coordinate z) HO.1 HM.2 HO.2.2.1 HO.2.2.2.1
    (commonDenominator ((G).state (parentKey hn ht ha hR0 false z)))
    (commonDenominator ((G).state (parentKey hn ht ha hR0 true z)))
    (commonDenominator_ne_zero _) (commonDenominator_ne_zero _) (parent_denominator_eq hn ht ha hR0 z hv)
  rw [rule_at_parent hn ht ha hR0 true z HC hg,rule_at_parent hn ht ha hR0 false z HC hg]
  simpa only [parentData,Bool.false_eq_true,ite_false,ite_true,meanReference] using HE

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
