/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointMembership
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProducerBounds
/-! # Actual provider fields construct the reserved ordinary parent hom -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
private theorem realizes_hom (F : IntegralMixedCutSource.Family) (key : List Bool) (values : ℕ→ℝ)
    (hh : IntegralMixedIntegerRealization.Realizes (F.state key) values) :
    ∃φ : (F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ ((F.state key).bank.numerator i)/((F.state key).bank.denominator i:ℝ)=values i.val :=by
  obtain ⟨_,φ,_,_,HV⟩:=hh
  exact ⟨φ,HV⟩
private theorem field_value_eq (a b : List Bool) (he : a=b)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (hb : FormulaSignSlotRadialProviderAtomic.Valid b) :
    FormulaSignSlotRadialProviderAtomic.field a ha=FormulaSignSlotRadialProviderAtomic.field b hb:=by cases he;rfl
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedIntegerRealization.Realizes
  FormulaSignSlotRadialProviderAtomic.field

theorem exists_field_interpretation (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    ∃φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ (((G).state (parentKey false z)).bank.numerator i)/
        (((G).state (parentKey false z)).bank.denominator i:ℝ)=
        FormulaSignSlotRadialProviderAtomic.field (atomic z) hv ((G).birth (parentKey false z)-1-i.val) :=by
  have HB:=parent_birth_actual false z hv
  have HH:=realizes_hom G (parentKey false z) (probeValues z hv) (probe_parent_realizes false z hv)
  obtain ⟨φ,Hφ⟩:=HH
  refine ⟨φ,fun i=>?_⟩
  have HI : i.val<creating z:=i.isLt.trans_eq HB
  have HT:=probeValues_field z hv i.val HI
  have HV:=before_probe_field z hv (creating z-1-i.val) (by omega)
  have HE : (G).birth (parentKey false z)-1-i.val=creating z-1-i.val:=
    congrArg (fun m : ℕ=>m-1-i.val) HB
  exact (Hφ i).trans (HT.trans (HV.trans
    (congrArg (FormulaSignSlotRadialProviderAtomic.field (atomic z) hv) HE.symm)))

theorem exists_original_interpretation (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (j : ℕ) :
    let z:=pair q (BinaryNatCode.encode j)
    ∃φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ (((G).state (parentKey false z)).bank.numerator i)/
        (((G).state (parentKey false z)).bank.denominator i:ℝ)=
        FormulaSignSlotRadialProviderAtomic.field q hv ((G).birth (parentKey false z)-1-i.val) :=by
  let z:=pair q (BinaryNatCode.encode j)
  have HQ : atomic z=q:=pairFst_pair _ _
  have HV : FormulaSignSlotRadialProviderAtomic.Valid (atomic z):=by rw [HQ];exact hv
  obtain ⟨φ,Hφ⟩:=exists_field_interpretation z HV
  have HF:=field_value_eq _ _ HQ HV hv
  exact ⟨φ,fun i=>(Hφ i).trans (congrFun HF _)⟩

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth creating

theorem row_good_of_valid (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (j : ℕ)
    (hj : FormulaSignSlotRadialProviderAtomic.depth q≤j) (hjn : j≤FormulaSignSlotRadialProviderAtomic.dimension q) :
    FormulaSignSlotRadialProviderProperRowWitness.RowGood (pair q (BinaryNatCode.encode j)) :=by
  have HM:=FormulaSignSlotRadialProviderProper.midpoint_good q hv hd
  have HFit:=FormulaSignSlotRadialProviderProper.mid_producer_before_probe q hv hd j hj hjn
  have HBirth : IntegralMixedRoadmapProper.midBirth (FormulaSignSlotRadialProviderAtomic.dimension q)
      (FormulaSignSlotRadialProviderAtomic.initial q) q≤creating (pair q (BinaryNatCode.encode j)):=by
    unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst at HFit
    omega
  rcases HM with ⟨HL,HA,HB,HLo,HUp,_,_⟩
  have HG : IntegralMixedChronologicalFrameCode.Good (FormulaSignSlotRadialProviderAtomic.dimension q)
      (creating (pair q (BinaryNatCode.encode j))) (IntegralMixedRoadmapProper.labels q):=
    ⟨HL.1,fun i hi=>(HL.2 i hi).trans_le HBirth⟩
  have HK:=IntegralMixedRoadmapProper.labels_count q
  have HD : IntegralMixedRoadmapAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth q:=by
    unfold IntegralMixedRoadmapAtomic.depth FormulaSignSlotRadialProviderAtomic.depth
      IntegralMixedRoadmapAtomic.payload FormulaSignSlotRadialProviderAtomic.payload
    rfl
  unfold FormulaSignSlotRadialProviderProperRowWitness.RowGood
  simp only [dimension,atomic,labels,oldProducer,offset,coordinate,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  refine ⟨⟨HG,HLo,HUp,?_,by omega⟩,HG,HA.trans_le HBirth,HB.trans_le HBirth,HLo,HUp,?_,by omega⟩ <;>
    unfold IntegralMixedRoadmapProper.levelIndex at * <;> omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
