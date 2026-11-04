/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
/-! # Every free index has a legal canonical ordinary row query -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedCriticalSweep IntegralMixedOriginalRegularSource IntegralMixedSelectedGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapProperRow.parentKey
 IntegralMixedRoadmapProperRow.dimension IntegralMixedRoadmapProperRow.initial IntegralMixedRoadmapProperRow.creating

theorem reference_rule_offset (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q)) :
    ((G).rule (oldKey hn ht ha hR0 q)).critical.offset.val=IntegralMixedRoadmapAtomic.depth q :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair] using hv
  have H:=IntegralMixedRoadmapProperRow.rule_offset hn ht ha hR0 false (rowKey q) HV HR
  have HD:=HB.1
  simpa only [oldKey,IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,
    IntegralMixedRoadmapProper.levelIndex,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HD))] using H

theorem free_global_le (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (i : Free ((G).rule (oldKey hn ht ha hR0 q))) :
    IntegralMixedRoadmapAtomic.depth q+i.val≤D q :=by
  have H:=i.isLt
  have HA : (G).ambient (oldKey hn ht ha hR0 q)=D q:=ambient_eq hn ht ha hR0 q
  have HO:=reference_rule_offset hn ht ha hR0 q hv HB HR
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  omega

theorem row_good_coordinate (q : List Bool)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (j : ℕ) (hj : IntegralMixedRoadmapAtomic.depth q≤j) (hjn : j≤D q) :
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (pair q (BinaryNatCode.encode j)) :=by
  have HD:=HB.1
  simp only [IntegralMixedRoadmapProperRowWitness.RowGood,IntegralMixedRoadmapProperRow.dimension,
    IntegralMixedRoadmapProperRow.creating,IntegralMixedRoadmapProperRow.initial,IntegralMixedRoadmapProperRow.oldPacket,
    IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.coordinate,
    IntegralMixedRoadmapProperRow.atomic,IntegralMixedRoadmapProperRow.oldProducer,rowKey,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits] at HR ⊢
  have HJ : WordListRecords.count (IntegralMixedRoadmapProper.labels q)+1≤j:=by
    rw [IntegralMixedRoadmapProper.labels_count]
    unfold IntegralMixedRoadmapProper.levelIndex
    omega
  exact ⟨⟨HR.1.1,HR.1.2.1,HR.1.2.2.1,HJ,by omega⟩,
    ⟨HR.2.1,HR.2.2.1,HR.2.2.2.1,HR.2.2.2.2.1,HR.2.2.2.2.2.1,HJ,by omega⟩⟩

theorem selected_free_value (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (i : Free ((G).rule (oldKey hn ht ha hR0 q))) :
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate G
      (IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false
        (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i.val))))
      (get (IntegralFramedBankQuery.Bank.parameters BK) Field.slot13
        (IntegralMixedRoadmapProperRow.parent hn ht ha hR0 false
          (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i.val)))))).val=i.val :=by
  have HG:=row_good_coordinate hn ht ha hR0 q HB HR (IntegralMixedRoadmapAtomic.depth q+i.val)
    (Nat.le_add_right _ _) (free_global_le hn ht ha hR0 q hv HB HR i)
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (IntegralMixedRoadmapProperRow.atomic (pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q+i.val)))):=by
    simpa only [IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have H:=IntegralMixedRoadmapProperRow.selected_coordinate hn ht ha hR0 false _ HV HG
  have HD:=HB.1
  simpa only [IntegralMixedRoadmapProperRow.relativeCoordinate,IntegralMixedRoadmapProperRow.coordinate,
    IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedRoadmapProper.levelIndex,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HD)),Nat.add_sub_cancel_left] using H

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
