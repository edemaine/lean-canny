/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateSearch
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProducerBounds
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointMembership
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperOrder
/-! # Native bounded coordinate search has its actual original-field Near meaning -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "Field"=>FormulaSignSlotRadialProviderAtomic.field
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderAtomic.field FormulaSignSlotRadialProviderProper.Base
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

noncomputable def CoordinateMeaning (right :Bool) (q :List Bool) (j :ℕ)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid q) :Prop:=
  let z:=pair q (BinaryNatCode.encode j)
  FormulaSignSlotRadialProviderProperRowWitness.RowGood z∧
  FormulaSignSlotRadialProviderProperRowWitness.SideGood right z∧
  CoordinateAt right z (Field q hv)

private theorem original_value_congr (a b :List Bool) (he :a=b)
    (ha :FormulaSignSlotRadialProviderAtomic.Valid a) (hb :FormulaSignSlotRadialProviderAtomic.Valid b) (i :ℕ) :
    originalValue a ha i=originalValue b hb i:=by
  subst b
  rfl

theorem coordinate_meaning (right :Bool) (q :List Bool) (j :ℕ)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB :FormulaSignSlotRadialProviderProper.Base q)
    (hj :FormulaSignSlotRadialProviderAtomic.depth q ≤ j) (hjn :j≤D q)
    (HSearch :FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right (pair q (BinaryNatCode.encode j))) :
    CoordinateMeaning right q j hv:=by
  obtain ⟨code,_,o,_,m,_,HL⟩:=HSearch
  let z:=pair q (BinaryNatCode.encode j)
  let u:=FormulaSignSlotRadialProviderProperRowWitness.packet z o m code
  have HLU:u∈FormulaSignSlotRadialProviderProperRowWitness.language right:=HL
  have HK:FormulaSignSlotRadialProviderProperRowWitness.key u=z:=by
    simp only [u,FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.key,pairFst_pair]
  have HAtomic:FormulaSignSlotRadialProviderProperRowWitness.atomic u=q:=by
    simp only [FormulaSignSlotRadialProviderProperRowWitness.atomic,HK,atomic,z,pairFst_pair]
  have HV:FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u):=by
    rw [HAtomic];exact hv
  have HZ:FormulaSignSlotRadialProviderAtomic.Valid (atomic z):=by
    simpa only [atomic,z,pairFst_pair] using hv
  have HR:FormulaSignSlotRadialProviderProperRowWitness.RowGood z:=by simpa only [HK] using HLU.1
  have HC:pointProducer false z<creating z:=by
    simpa only [z,pointProducer,dimension,initial,atomic,coordinate,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,Bool.false_eq_true,ite_false] using
      FormulaSignSlotRadialProviderProper.child_producer_before_probe q hv j hj hjn
  have HBase:=HB
  unfold FormulaSignSlotRadialProviderProper.Base at HBase
  have HM:pointProducer true z<creating z:=by
    simpa only [z,pointProducer,dimension,initial,atomic,coordinate,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,ite_true] using
      FormulaSignSlotRadialProviderProper.mid_producer_before_probe q hv HBase.1 j hj hjn
  have HVal:∀i,i<creating z → originalValues u HV i=Field q hv i:=by
    intro i hi
    have HF:=before_probe_field z HZ i hi
    have HE:=original_value_congr _ _ HAtomic HV hv i
    exact HE.trans (by simpa only [atomic,z,pairFst_pair] using HF)
  have HA:originalValues u HV (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u))<
      originalValues u HV (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    rw [HK,HVal _ HR.2.2.1,HVal _ HR.2.2.2.1]
    simpa only [oldProducer,atomic,z,pairFst_pair] using
      FormulaSignSlotRadialProviderProper.order_of_base q hv HB
  have HChild:pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u):=by simpa only [HK] using HC
  have HMid:pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u):=by simpa only [HK] using HM
  have HO:=native_coordinate_outcome right u HV HLU HChild HMid HA
  unfold CoordinateOutcome at HO
  rw [HK] at HO
  unfold CoordinateAt at HO
  obtain ⟨φ,Hφ,HNear⟩:=HO
  have HBth:=parent_birth_actual false z HZ
  have HFields:QuotientsAt G (parentKey false z) φ (Field q hv):=by
    intro i
    exact (Hφ i).trans (HVal _ (by have HI:=i.isLt;omega))
  rw [HVal _ HR.2.2.1,HVal _ HR.2.2.2.1,HVal _ HC,HVal _ HM] at HNear
  have HEndpoint:oldProducer right z<creating z:=by
    cases right
    · exact HR.2.2.1
    · exact HR.2.2.2.1
  rw [HVal _ HEndpoint] at HNear
  unfold CoordinateMeaning
  refine ⟨HR,?_,?_⟩
  · simpa only [HK] using HLU.2.1
  · exact ⟨φ,HFields,HNear⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
