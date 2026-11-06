/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowCoordinateTransport
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalBad
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderLocalEdge
public import LeanCanny.Geometry.IntegralMixedSelectedNearTransport
/-! # Native coordinate guards give a path from the child to its physical MID -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem original_quotient_agreement (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (values : ℕ→ℝ) (φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : B.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=values (A.birth-1-i.val))
    (Hψ : ∀i,ψ (B.state.bank.numerator i)/(B.state.bank.denominator i:ℝ)=values (B.birth-1-i.val)) :
    ∀(i : Fin A.birth) (j : Fin B.birth),i.val=j.val→
      φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=
      ψ (B.state.bank.numerator j)/(B.state.bank.denominator j:ℝ) :=by
  have HB:=congrArg IntegralMixedPrefixSnapshot.Data.birth he
  intro i j hij
  rw [Hφ i,Hψ j]
  exact congrArg values (by omega)

private theorem side_good_pair (right : Bool) (q w : List Bool)
    (H : FormulaSignSlotRadialProviderProperRowWitness.SideGood right (pair q w)) :
    IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q)
      (IntegralMixedRoadmapProper.levelIndex q)=if right then [true] else [] :=by
  simpa only [FormulaSignSlotRadialProviderProperRowWitness.SideGood,
    FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using H

private theorem side_value (right : Bool) (w : List Bool) (values : Bool→ℝ)
    (H : w=if right then [true] else []) :
    (if w=[true] then values true else values false)=values right :=by
  rw [H]
  cases right <;> simp

local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
 FormulaSignSlotRadialProviderRecordPlan.certifiedPlan FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
private theorem actual_family :IntegralMixedFramedHistoryFamilyBits.family
    (BK).parameters (BK).plan (BK).data=G:=rfl
private theorem raw_depth (q :List Bool) :IntegralMixedRoadmapAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth q:=rfl
private theorem raw_payload (q :List Bool) :IntegralMixedRoadmapAtomic.payload q=FormulaSignSlotRadialProviderAtomic.payload q:=rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
 FormulaSignSlotRadialProviderAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
 IntegralMixedRoadmapProper.labels field midpoint child
 FormulaSignSlotRadialProviderProperRow.parentKey FormulaSignSlotRadialProviderProperRow.parent
 FormulaSignSlotRadialProviderProperRow.root FormulaSignSlotRadialProviderProperRow.creating

attribute [local semireducible] FormulaSignSlotRadialProviderRecordPlan.bank

private noncomputable def NumericalMeaning (F :IntegralMixedCutSource.Family) (p :IntegralCriticalHistoryTask.Parameters) (right : Bool) (q : List Bool) (j : ℕ)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) : Prop:=
  let z:=pair q (BinaryNatCode.encode j)
  let old:=FormulaSignSlotRadialProviderProperRow.parentKey false z
  FormulaSignSlotRadialProviderProperRowWitness.RowGood z ∧
  FormulaSignSlotRadialProviderProperRowWitness.SideGood right z ∧
  ∃φ : ((F).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ (((F).state old).bank.numerator i)/(((F).state old).bank.denominator i:ℝ)=
      FormulaSignSlotRadialProviderProperLocalFrame.field q hv ((F).birth old-1-i.val)) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near ((F).state old) ((F).birth_bound old) ((F).rule old) φ
      (FormulaSignSlotRadialProviderProperLocalFrame.field q hv (IntegralMixedRoadmapProper.producer false q))
      (FormulaSignSlotRadialProviderProperLocalFrame.field q hv (IntegralMixedRoadmapProper.producer true q))
      (FormulaSignSlotRadialProviderProperLocalFrame.field q hv (IntegralMixedRoadmapProper.producer right q))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate F old (IntegralCriticalHistoryTask.get p IntegralCriticalHistoryTask.Field.slot13 (FormulaSignSlotRadialProviderProperRow.parent false z)))
      (IntegralMixedSelectedRootRank.rank ((F).state old) ((F).birth_bound old) ((F).rule old) φ
        ((FormulaSignSlotRadialProviderProperLocalFrame.field q hv (IntegralMixedRoadmapProper.producer false q)+
          FormulaSignSlotRadialProviderProperLocalFrame.field q hv (IntegralMixedRoadmapProper.producer true q))/2)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate F old (IntegralCriticalHistoryTask.get p IntegralCriticalHistoryTask.Field.slot13 (FormulaSignSlotRadialProviderProperRow.parent false z)))
        (FormulaSignSlotRadialProviderProperLocalFrame.field q hv
          (IntegralMixedRoadmapProper.midProducer (FormulaSignSlotRadialProviderAtomic.dimension q)
            (FormulaSignSlotRadialProviderAtomic.initial q) q j)))
      (FormulaSignSlotRadialProviderProperLocalFrame.field q hv
        (IntegralMixedRoadmapProper.childProducer (FormulaSignSlotRadialProviderAtomic.dimension q)
          (FormulaSignSlotRadialProviderAtomic.initial q) q j))


private noncomputable abbrev ActualCoordinateMeaning (right :Bool) (q :List Bool) (j :ℕ)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid q):=NumericalMeaning G P right q j hv


private theorem actual_coordinate_meaning (right :Bool) (q :List Bool) (j :ℕ)
    (hv :FormulaSignSlotRadialProviderAtomic.Valid q) (HB :FormulaSignSlotRadialProviderProper.Base q)
    (hj :FormulaSignSlotRadialProviderAtomic.depth q ≤ j) (hjn :j≤D q)
    (HS :FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right (pair q (BinaryNatCode.encode j))) :
    ActualCoordinateMeaning right q j hv:=by
  have HM:=FormulaSignSlotRadialProviderProperRow.coordinate_meaning right q j hv HB hj hjn HS
  have HM0:NumericalMeaning (IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data)
      (BK).parameters right q j hv:=by
    unfold FormulaSignSlotRadialProviderProperRow.CoordinateMeaning FormulaSignSlotRadialProviderProperRow.CoordinateAt
      FormulaSignSlotRadialProviderProperRow.QuotientsAt at HM
    unfold NumericalMeaning
    simpa only [field,FormulaSignSlotRadialProviderProperRow.oldProducer,
      FormulaSignSlotRadialProviderProperRow.pointProducer,FormulaSignSlotRadialProviderProperRow.dimension,
      FormulaSignSlotRadialProviderProperRow.initial,FormulaSignSlotRadialProviderProperRow.atomic,
      FormulaSignSlotRadialProviderProperRow.coordinate,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,
      Nat.fromBitsLE_bits,Bool.false_eq_true,ite_false,ite_true] using HM
  have HE:(IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data,(BK).parameters)=(G,P):=rfl
  exact Eq.mp (congrArg (fun t=>NumericalMeaning t.1 t.2 right q j hv) HE) HM0


private theorem actual_order_of_base (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB :FormulaSignSlotRadialProviderProper.Base q) :
    field q hv (IntegralMixedRoadmapProper.producer false q)<field q hv (IntegralMixedRoadmapProper.producer true q):=by
  simpa only [field] using FormulaSignSlotRadialProviderProper.order_of_base q hv HB

private def BadFreeAt (F :IntegralMixedCutSource.Family) (key :List Bool) (values :ℕ→ℝ)
    (a b :ℕ):Prop:=
  ∀φ:(F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ ((F.state key).bank.numerator i)/((F.state key).bank.denominator i:ℝ)=values (F.birth key-1-i.val))→
    ∀c:IntegralMixedRelativeCuts.Choices (F.state key) (F.birth_bound _) (F.rule key) φ,
    ∀t,t∈Set.Ioo (values a) (values b)→
      t∉IntegralMixedSelectedCriticalCuts.bad (F.state key) (F.birth_bound _) (F.rule key) φ c

private theorem actual_no_bad_of_base (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB :FormulaSignSlotRadialProviderProper.Base q)
    (HR :FormulaSignSlotRadialProviderProperRowWitness.RowGood (rowKey q))
    (φ :((G).state (oldKey q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ :∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=field q hv ((G).birth (oldKey q)-1-i.val))
    (c :IntegralMixedRelativeCuts.Choices ((G).state (oldKey q)) ((G).birth_bound _) ((G).rule (oldKey q)) φ) :
    ∀a,a∈Set.Ioo (field q hv (IntegralMixedRoadmapProper.producer false q))
      (field q hv (IntegralMixedRoadmapProper.producer true q))→
      a∉IntegralMixedSelectedCriticalCuts.bad ((G).state (oldKey q)) ((G).birth_bound _) ((G).rule (oldKey q)) φ c:=by

  have HV:FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic (rowKey q)):=by
    simpa only [FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair] using hv
  have HB0:FormulaSignSlotRadialProviderProper.Base (FormulaSignSlotRadialProviderProperRow.atomic (rowKey q)):=by
    simpa only [FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair] using HB
  have HN:BadFreeAt (IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data)
      (FormulaSignSlotRadialProviderProperRow.parentKey false (rowKey q))
      (FormulaSignSlotRadialProviderProperRow.originalValue q hv)
      (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q):=by
    intro ψ Hψ cs
    have Hψ0:FormulaSignSlotRadialProviderProperRow.QuotientsAt
        (IntegralMixedFramedHistoryFamilyBits.family (BK).parameters (BK).plan (BK).data)
        (FormulaSignSlotRadialProviderProperRow.parentKey false (rowKey q)) ψ
        (FormulaSignSlotRadialProviderProperRow.originalValue
          (FormulaSignSlotRadialProviderProperRow.atomic (rowKey q)) HV):=by
      unfold FormulaSignSlotRadialProviderProperRow.QuotientsAt
      simpa only [FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair] using Hψ
    have HH:=FormulaSignSlotRadialProviderProperRow.no_bad_of_base (rowKey q) HV HB0 HR ψ Hψ0 cs
    simpa only [FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair,
      FormulaSignSlotRadialProviderProperRow.oldProducer] using HH
  have HN0:=Eq.mp (congrArg (fun F=>BadFreeAt F (oldKey q)
    (FormulaSignSlotRadialProviderProperRow.originalValue q hv)
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)) actual_family) HN
  have HN1:=HN0 φ (quotients_original q hv φ Hφ) c
  have HL:=FormulaSignSlotRadialProviderProperRow.before_probe_field (rowKey q) HV _ HR.2.2.1
  have HRv:=FormulaSignSlotRadialProviderProperRow.before_probe_field (rowKey q) HV _ HR.2.2.2.1
  simp only [FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair,
    FormulaSignSlotRadialProviderProperRow.oldProducer] at HL HRv
  rw [HL,HRv] at HN1
  simpa only [field] using HN1

private theorem coordinates_near (right : Bool) (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB : FormulaSignSlotRadialProviderProper.Base q)
    (HAll : FormulaSignSlotRadialProviderLocalEdge.allCoordinates right q)
    (HR : FormulaSignSlotRadialProviderProperRowWitness.RowGood (rowKey q))
    (φ : ((G).state (oldKey q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey q)).bank.numerator i)/
      (((G).state (oldKey q)).bank.denominator i:ℝ)=
        field q hv ((G).birth (oldKey q)-1-i.val)) :
    ∀i : Free ((G).rule (oldKey q)),
      IntegralMixedSelectedCoordinateEndpoint.Near ((G).state (oldKey q))
        ((G).birth_bound _) ((G).rule (oldKey q)) φ
        (field q hv (IntegralMixedRoadmapProper.producer false q))
        (field q hv (IntegralMixedRoadmapProper.producer true q))
        (field q hv (IntegralMixedRoadmapProper.producer right q)) i
        (IntegralMixedSelectedRootRank.rank ((G).state (oldKey q)) ((G).birth_bound _)
          ((G).rule (oldKey q)) φ
          ((field q hv (IntegralMixedRoadmapProper.producer false q)+
            field q hv (IntegralMixedRoadmapProper.producer true q))/2) i
          (midpoint q hv (ClearedCoordinateCritical.freeIndex
            ((G).rule (oldKey q)).critical.offset.val
            (fit ((G).rule (oldKey q))).le i)))
        (child q hv (ClearedCoordinateCritical.freeIndex
          ((G).rule (oldKey q)).critical.offset.val
          (fit ((G).rule (oldKey q))).le i)) :=by
  intro i
  let j:=FormulaSignSlotRadialProviderAtomic.depth q+i.val
  have HV : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hv
  have HO0:=FormulaSignSlotRadialProviderProperRow.rule_offset false (rowKey q) HV HR
  have HL : FormulaSignSlotRadialProviderProperRow.offset (rowKey q)=FormulaSignSlotRadialProviderAtomic.depth q:=by
    unfold FormulaSignSlotRadialProviderProperRow.offset IntegralMixedRoadmapProper.levelIndex
    have HP:=HB.1
    simp only [raw_depth]
    simp only [rowKey,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair]
    omega
  have HO : ((G).rule (oldKey q)).critical.offset.val=FormulaSignSlotRadialProviderAtomic.depth q:=HO0.trans HL
  have HD:=ambient_eq q
  have HI : i.val<ambient q-FormulaSignSlotRadialProviderAtomic.depth q+1:=by
    simpa only [Free,HO,ambient] using i.isLt
  have HF:= (fit ((G).rule (oldKey q))).le
  have HJ : j≤D q:=by dsimp only [j];unfold ambient at HD HI;omega
  have HC : i.val<FormulaSignSlotRadialProviderLocalEdge.count q:=by
    unfold FormulaSignSlotRadialProviderLocalEdge.count IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
    simp only [raw_depth]
    have HP:=HB.1
    dsimp only [j] at HJ
    omega
  have HSearch:=HAll i.val HC
  simp only [FormulaSignSlotRadialProviderLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,List.length_replicate] at HSearch
  have HJlo : FormulaSignSlotRadialProviderAtomic.depth q≤j:=by dsimp only [j];omega
  obtain ⟨HRj,_,ψ,Hψ,HNear⟩:=actual_coordinate_meaning right q j hv HB HJlo HJ HSearch
  have HE:=FormulaSignSlotRadialProviderProperRow.parent_coordinate_snapshot_eq q
    (BinaryNatCode.encode j) (BinaryNatCode.encode (FormulaSignSlotRadialProviderAtomic.depth q)) hv
  have HS:=FormulaSignSlotRadialProviderProperRow.ordinary_coordinate_shape q
    (BinaryNatCode.encode j) (BinaryNatCode.encode (FormulaSignSlotRadialProviderAtomic.depth q)) hv HRj HR
  let oldj:=FormulaSignSlotRadialProviderProperRow.parentKey false (pair q (BinaryNatCode.encode j))
  let selectedj:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldj
    (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13
      (FormulaSignSlotRadialProviderProperRow.parent false (pair q (BinaryNatCode.encode j))))
  have HVa : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic (pair q (BinaryNatCode.encode j))):=by
    simpa only [FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hv
  have HSelected : selectedj.val=i.val:=by
    have HX:=FormulaSignSlotRadialProviderProperRow.selected_coordinate false
      (pair q (BinaryNatCode.encode j)) HVa HRj
    have HEindex : FormulaSignSlotRadialProviderProperRow.relativeCoordinate (pair q (BinaryNatCode.encode j))=i.val:=by
      unfold FormulaSignSlotRadialProviderProperRow.relativeCoordinate
      have HLj : FormulaSignSlotRadialProviderProperRow.offset (pair q (BinaryNatCode.encode j))=FormulaSignSlotRadialProviderAtomic.depth q:=by
        simpa only [FormulaSignSlotRadialProviderProperRow.offset,FormulaSignSlotRadialProviderProperRow.atomic,rowKey,pairFst_pair] using HL
      rw [HLj]
      simp only [FormulaSignSlotRadialProviderProperRow.coordinate,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,j,Nat.add_sub_cancel_left]
    exact HX.trans HEindex
  have HAgreement:=original_quotient_agreement
    (IntegralMixedPrefixSnapshot.ofState ((G).state oldj))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey q))) HE
    (field q hv) ψ φ Hψ Hφ
  have HCj:=FormulaSignSlotRadialProviderProperRow.parent_canonical false
    (pair q (BinaryNatCode.encode j)) (FormulaSignSlotRadialProviderProperRow.row_count_positive _ HVa)
  have HTransfer:=IntegralMixedSelectedNearTransport.anchored_near_iff_of_snapshot
    (IntegralMixedPrefixSnapshot.ofState ((G).state oldj))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (oldKey q))) HE HCj
    ((G).birth_bound _) ((G).birth_bound _) ((G).rule oldj) ((G).rule (oldKey q))
    HS ψ φ HAgreement selectedj i HSelected
    (field q hv (IntegralMixedRoadmapProper.producer false q))
    (field q hv (IntegralMixedRoadmapProper.producer true q))
    (field q hv (IntegralMixedRoadmapProper.producer right q))
    ((field q hv (IntegralMixedRoadmapProper.producer false q)+
      field q hv (IntegralMixedRoadmapProper.producer true q))/2)
    (field q hv (IntegralMixedRoadmapProper.midProducer (D q) (N q) q j))
    (field q hv (IntegralMixedRoadmapProper.childProducer (D q) (N q) q j))
  have HT:=HTransfer.mp HNear
  let ix : Fin (ambient q+1):=ClearedCoordinateCritical.freeIndex ((G).rule (oldKey q)).critical.offset.val HF i
  have Hix : ix.val=j:=congrArg (fun k : ℕ=>k+i.val) HO
  have HM:=midpoint_free q hv HB ix (by rw [Hix];exact HJlo)
  have HH:=child_free q hv ix (by rw [Hix];exact HJlo)
  rw [Hix] at HM HH
  rw [HM,HH]
  exact HT

private theorem joined_of_side (right : Bool) (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (HB : FormulaSignSlotRadialProviderProper.Base q)
    (HAll : FormulaSignSlotRadialProviderLocalEdge.allCoordinates right q) :
    JoinedIn {p : Fin (ambient q+1)→ℝ |
      (FermatCriticalHomogenization.polynomial ((G).spatial (oldKey q)).low
        ((G).spatial (oldKey q)).leading ((G).spatial (oldKey q)).degree).eval₂
        (Int.castRingHom ℝ) p=0} (child q hv) (midpoint q hv) :=by
  have HD:=FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HP:=HB.1
  have HC : 0<FormulaSignSlotRadialProviderLocalEdge.count q:=by
    unfold FormulaSignSlotRadialProviderLocalEdge.count IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
    simp only [raw_depth]
    omega
  have HSearch:=HAll 0 HC
  simp only [FormulaSignSlotRadialProviderLocalEdge.coordinateKey,pairFst_pair,pairSnd_pair,
    List.length_replicate,Nat.add_zero] at HSearch
  obtain ⟨HR,HS,φ,Hφ,_⟩:=actual_coordinate_meaning right q
    (FormulaSignSlotRadialProviderAtomic.depth q) hv HB (Nat.le_refl _) HD HSearch
  have HPhysical:=midpoint_physical q hv HB HR φ Hφ
  have HFrozen:=child_frozen q hv HB HR φ Hφ
  have HSide:=side_good_pair right q (BinaryNatCode.encode (FormulaSignSlotRadialProviderAtomic.depth q)) HS
  have HEndpoint:=side_value right _
    (fun side=>field q hv (IntegralMixedRoadmapProper.producer side q)) HSide
  have HFrozenRight:=Eq.mp (congrArg (fun e : ℝ=>
    IntegralMixedSelectedCoordinateEndpoint.Frozen ((G).state (oldKey q))
      ((G).birth_bound _) ((G).rule (oldKey q)) φ e (child q hv)) HEndpoint) HFrozen
  have HOrder:=actual_order_of_base q hv HB
  let a:=field q hv (IntegralMixedRoadmapProper.producer false q)
  let b:=field q hv (IntegralMixedRoadmapProper.producer true q)
  let e:=field q hv (IntegralMixedRoadmapProper.producer right q)
  have HAB : a<b:=HOrder
  let t₀ : Ioo a b:=⟨(a+b)/2,by constructor <;> linarith⟩
  have HE : e∈Icc a b:=by
    cases right
    · exact ⟨le_refl _,le_of_lt HAB⟩
    · exact ⟨le_of_lt HAB,le_refl _⟩
  have HChoices:=IntegralMixedRelativeCuts.exists_choices ((G).state (oldKey q))
    ((G).birth_bound _) ((G).rule (oldKey q)) φ
  obtain ⟨c⟩:=HChoices
  exact IntegralMixedSelectedCoordinateEndpoint.joined_source_of_near
    ((G).state (oldKey q)) ((G).birth_bound _) ((G).rule (oldKey q)) φ c t₀
    (actual_no_bad_of_base q hv HB HR φ Hφ c)
    ⟨midpoint q hv,HPhysical⟩ e HE (child q hv) HFrozenRight
    (coordinates_near right q hv HB HAll HR φ Hφ)

/-- Every accepted native local incidence joins its actual child point to its
actual physical midpoint. The no-critical conjunct is unnecessary for soundness. -/
theorem local_joined (q : List Bool) (H : FormulaSignSlotRadialProviderLocalEdge.Local q) :
    JoinedIn {p : Fin (ambient q+1)→ℝ |
      (FermatCriticalHomogenization.polynomial ((G).spatial (oldKey q)).low
        ((G).spatial (oldKey q)).leading ((G).spatial (oldKey q)).degree).eval₂
        (Int.castRingHom ℝ) p=0} (child q H.1) (midpoint q H.1) :=by
  rcases H.2.2.2 with HL|HR
  · exact joined_of_side false q H.1 H.2.1 HL
  · exact joined_of_side true q H.1 H.2.1 HR

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
