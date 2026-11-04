/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
public import LeanCanny.Encoding.IntegralMixedPhysicalCutEndpointField
/-! # The proper native order test orders the original endpoint fields

The order context has the same literal root and complete word as the
atomic node. The verified full-input context transport supplies its tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "OC"=>IntegralMixedRoadmapProper.orderContext hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalSquare.point IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

theorem order_context_root (q : List Bool) : pairFst (OC q)=pairFst (IntegralMixedRoadmapAtomic.context q) :=by
  simp only [IntegralMixedRoadmapProper.orderContext,IntegralMixedRoadmapAtomic.context,pairFst_pair]

theorem order_selected (right : Bool) (q : List Bool) :
    IntegralMixedPhysicalCutOpenInterval.selected right (OC q)=
      IntegralMixedRoadmapProper.endpointIndex hn ht ha hR0 right q :=by
  cases right <;> simp only [IntegralMixedPhysicalCutOpenInterval.selected,IntegralMixedRoadmapProper.orderContext,
    Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

private theorem count_field (c : List Bool) : IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false c=
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) c :=rfl

theorem order_count (q : List Bool) : IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (OC q)=
    IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q :=by
  rw [count_field hn ht ha hR0]
  have HE:=congrArg ((G).birth) (IntegralMixedPhysicalMarkedContext.key_eq hn ht ha (radius_binary hR0)
    (OC q) (IntegralMixedRoadmapAtomic.context q) (order_context_root hn ht ha hR0 q))
  exact HE

theorem order_valid (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    SquareSampleCompleteVertices.Valid S (OC q) (IntegralMixedRoadmapAtomic.word q) :=
  (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (OC q) (IntegralMixedRoadmapAtomic.word q)
    (order_context_root hn ht ha hR0 q).symm).mp (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)

theorem order_selected_lt (right : Bool) (q : List Bool) :
    IntegralMixedPhysicalCutOpenInterval.selected right (OC q)<
      IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (OC q) :=by
  have HP:=IntegralMixedPhysicalFieldEquality.count_pos hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context q)
  change 0<IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q at HP
  rw [order_selected,order_count]
  unfold IntegralMixedRoadmapProper.endpointIndex
  omega

attribute [local irreducible] IntegralMixedPhysicalFieldEquality.point
  IntegralMixedPhysicalFieldEquality.pointNewest field

theorem order_endpoint (right : Bool) (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hb : IntegralMixedRoadmapProper.producer right q<IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q) :
    IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false right (OC q)
      (IntegralMixedRoadmapAtomic.word q) (order_valid hn ht ha hR0 q hv) (order_selected_lt hn ht ha hR0 right q)=
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer right q) :=by
  have HE:=IntegralMixedPhysicalCutEndpointField.endpoint_field hn ht ha hR0 (OC q)
    (IntegralMixedRoadmapAtomic.word q) (order_valid hn ht ha hR0 q hv) right (order_selected_lt hn ht ha hR0 right q)
  rw [order_selected] at HE
  have HC:=IntegralMixedPhysicalMarkedContext.pointNewest_eq hn ht ha (radius_binary hR0) (OC q)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (order_context_root hn ht ha hR0 q) (order_valid hn ht ha hR0 q hv)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
    (IntegralMixedRoadmapProper.endpointIndex hn ht ha hR0 right q)
  refine HE.trans (HC.trans ?_)
  unfold field IntegralMixedPhysicalFieldEquality.point
  apply congrArg (IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv))
  unfold IntegralMixedRoadmapProper.endpointIndex IntegralMixedPhysicalFieldEquality.newest
  change IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q-1-IntegralMixedRoadmapProper.producer right q=
    IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q-1-
      min (IntegralMixedRoadmapProper.producer right q) (IntegralMixedRoadmapProper.fullCount hn ht ha hR0 q-1)
  rw [min_eq_left (by omega)]

theorem order_of_base (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q) :
    field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)<
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q) :=by
  have HH : IntegralMixedPhysicalCutOrderedInterval.order hn ht ha (radius_binary hR0) false
      (pair (OC q) (IntegralMixedRoadmapAtomic.word q))=InfinitesimalSign.encode 1:=by
    simpa only [IntegralMixedRoadmapProper.order,Function.comp_apply,IntegralMixedRoadmapProper.orderQuery] using HB.2.2.2.2
  have HE:=(IntegralMixedPhysicalCutOrderedInterval.order_iff hn ht ha (radius_binary hR0) false (OC q)
    (IntegralMixedRoadmapAtomic.word q) (order_valid hn ht ha hR0 q hv)
    (order_selected_lt hn ht ha hR0 false q) (order_selected_lt hn ht ha hR0 true q)).mp HH
  rw [order_endpoint hn ht ha hR0 false q hv HB.2.1.1,order_endpoint hn ht ha hR0 true q hv HB.2.1.2] at HE
  exact HE

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
