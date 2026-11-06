/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperBase
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBankContext
/-! # Native provider Base ordering is ordering of the actual own endpoint fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
  (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "OC"=>orderContext
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalBankTerm.env

private theorem order_context_root (q :List Bool) :pairFst (OC q)=pairFst (FormulaSignSlotRadialProviderAtomic.context q):=by
  simp only [orderContext,FormulaSignSlotRadialProviderAtomic.context,pairFst_pair]
private theorem order_selected (right :Bool) (q :List Bool) :
    FormulaSignSlotRadialProviderCutInterval.selected right (OC q)=endpointIndex right q:=by
  cases right <;> simp only [FormulaSignSlotRadialProviderCutInterval.selected,orderContext,
    Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem order_count (q :List Bool) :FormulaSignSlotRadialProviderCutInterval.count (OC q)=fullCount q:=by
  have HE:=congrArg ((G).birth) (FormulaSignSlotRadialProviderBankContext.key_eq
    (OC q) (FormulaSignSlotRadialProviderAtomic.context q) (order_context_root q))
  exact HE
private theorem order_valid (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q) :
    SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (OC q)
      (FormulaSignSlotRadialProviderAtomic.word q):=
  (FormulaSignSlotRadialProviderBankContext.valid_iff (FormulaSignSlotRadialProviderAtomic.context q)
    (OC q) (FormulaSignSlotRadialProviderAtomic.word q) (order_context_root q).symm).mp
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
private theorem order_selected_lt (right :Bool) (q :List Bool) :
    FormulaSignSlotRadialProviderCutInterval.selected right (OC q)<FormulaSignSlotRadialProviderCutInterval.count (OC q):=by
  have HP:=FormulaSignSlotRadialProviderFieldEquality.count_pos (FormulaSignSlotRadialProviderAtomic.context q)
  change 0<fullCount q at HP
  rw [order_selected,order_count]
  unfold endpointIndex
  omega

private theorem order_endpoint (right :Bool) (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (hb :producer right q<fullCount q) :
    FormulaSignSlotRadialProviderCutInterval.endpoint right (OC q) (FormulaSignSlotRadialProviderAtomic.word q)
      (order_valid q hv) (order_selected_lt right q)=FormulaSignSlotRadialProviderAtomic.field q hv (producer right q):=by
  have HE:=FormulaSignSlotRadialProviderCutInterval.endpoint_env right (OC q)
    (FormulaSignSlotRadialProviderAtomic.word q) (order_valid q hv) (order_selected_lt right q)
  rw [order_selected,order_count] at HE
  have HI:fullCount q-1-endpointIndex right q=producer right q:=by unfold endpointIndex;omega
  rw [HI] at HE
  have HOld:=FormulaSignSlotRadialProviderFieldEquality.point_env (OC q)
    (FormulaSignSlotRadialProviderAtomic.word q) (order_valid q hv) (producer right q)
    (show producer right q<FormulaSignSlotRadialProviderFieldEquality.count (OC q) from
      hb.trans_eq (order_count q).symm)
  have HNew:=FormulaSignSlotRadialProviderFieldEquality.point_env (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
    (producer right q) hb
  have HSame:=FormulaSignSlotRadialProviderBankContext.point_eq (OC q) (FormulaSignSlotRadialProviderAtomic.context q)
    (FormulaSignSlotRadialProviderAtomic.word q) (order_context_root q) (order_valid q hv)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (producer right q)
  exact HE.trans (HOld.symm.trans (HSame.trans HNew))

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.field
  FormulaSignSlotRadialProviderAtomic.Valid Base order
  FormulaSignSlotRadialProviderCutInterval.order

theorem order_of_base (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q) (HB :Base q) :
    FormulaSignSlotRadialProviderAtomic.field q hv (producer false q)<
      FormulaSignSlotRadialProviderAtomic.field q hv (producer true q):=by
  unfold Base at HB
  have HH:FormulaSignSlotRadialProviderCutInterval.order
      (pair (OC q) (FormulaSignSlotRadialProviderAtomic.word q))=InfinitesimalSign.encode 1:=by
    simpa only [order,orderQuery,Function.comp_apply] using HB.2.2.2.2
  have HE:=(FormulaSignSlotRadialProviderCutInterval.order_iff (OC q)
    (FormulaSignSlotRadialProviderAtomic.word q) (order_valid q hv)
    (order_selected_lt false q) (order_selected_lt true q)).mp HH
  rw [order_endpoint false q hv HB.2.1.1,order_endpoint true q hv HB.2.1.2] at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
