/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointRank
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRankComplete
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNearComplete
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProducerBounds
public import LeanCanny.Encoding.FixedWidthNatVector
/-! # Genuine coordinate Near has two fresh, bounded native statistic words -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem value_eq (a b : List Bool) (he : a=b)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (hb : FormulaSignSlotRadialProviderAtomic.Valid b) :
    originalValue a ha=originalValue b hb :=by cases he;rfl
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "BP"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "BH"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  CoordinateAt CoordinateOutcome originalValue

private def RowSemantics (right : Bool) (z : List Bool) (values : ℕ→ℝ) (rwrd : List Bool) : Prop:=
  let old:=parentKey false z
  let j:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent false z))
  let a:=(values (oldProducer false z)+values (oldProducer true z))/2
  ∃φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
      values ((G).birth old-1-i.val)) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near ((G).state old) ((G).birth_bound old) ((G).rule old) φ
      (values (oldProducer false z)) (values (oldProducer true z)) (values (oldProducer right z)) j
      (Nat.fromBitsLE rwrd) (values (pointProducer false z)) ∧
    values (pointProducer true z)∈IntegralMixedFrozenFrameSectionCode.roots
      ((G).state old) ((G).birth_bound old) ((G).rule old) φ a j ∧
    Nat.fromBitsLE rwrd=IntegralMixedSelectedRootRank.rank ((G).state old) ((G).birth_bound old) ((G).rule old) φ a j
      (values (pointProducer true z))

attribute [local irreducible] RowSemantics

theorem row_producer_bounds (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    pointProducer false z<creating z ∧ pointProducer true z<creating z :=by
  have HE : IntegralMixedRoadmapAtomic.depth (atomic z)=FormulaSignSlotRadialProviderAtomic.depth (atomic z):=rfl
  have HO : offset z=FormulaSignSlotRadialProviderAtomic.depth (atomic z):=by
    unfold offset IntegralMixedRoadmapProper.levelIndex
    rw [HE]
    omega
  have HJ0 : offset z≤coordinate z:=by rw [offset_count];exact hr.1.2.2.2.1
  have HJ : FormulaSignSlotRadialProviderAtomic.depth (atomic z)≤coordinate z:=HO ▸ HJ0
  have HN : coordinate z≤dimension z:=by have HH:=hr.1.2.2.2.2;omega
  have HC:=FormulaSignSlotRadialProviderProper.child_producer_before_probe (atomic z) hv (coordinate z) HJ HN
  have HM:=FormulaSignSlotRadialProviderProper.mid_producer_before_probe (atomic z) hv hd (coordinate z) HJ HN
  constructor
  · simpa only [pointProducer,Bool.false_eq_true,ite_false,dimension,initial,creating,oldPacket,atomic,pairFst_pair] using HC
  · simpa only [pointProducer,ite_true,dimension,initial,creating,oldPacket,atomic,pairFst_pair] using HM

theorem holds_of_coordinate_at (right : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (hs : FormulaSignSlotRadialProviderProperRowWitness.SideGood right z)
    (hab : originalValue (atomic z) hv (oldProducer false z)<originalValue (atomic z) hv (oldProducer true z))
    (hMeaning : CoordinateAt right z (originalValue (atomic z) hv)) :
    FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right z :=by
  unfold CoordinateAt QuotientsAt at hMeaning
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at hMeaning
  obtain ⟨φ,Hφ,HNear⟩:=hMeaning
  let old:=parentKey false z
  let coord:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent false z))
  let meanValue:=(originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2
  let midValue:=originalValue (atomic z) hv (pointProducer true z)
  let rank:=IntegralMixedSelectedRootRank.rank ((G).state old) ((G).birth_bound old) ((G).rule old) φ meanValue coord midValue
  have HMem:=midpoint_coordinate_mem z hv hd hr φ Hφ
  have HBound : rank<2^FormulaSignSlotRadialProviderAtomic.width (atomic z):=midpoint_rank_bounded z hv hd hr φ Hφ
  let rwrd:=List.ofFn (fun k : Fin (FormulaSignSlotRadialProviderAtomic.width (atomic z))=>rank.testBit k.val)
  have HRLen : rwrd.length=FormulaSignSlotRadialProviderProperCoordinateSearch.rankWidth z:=by
    simp only [rwrd,List.length_ofFn,FormulaSignSlotRadialProviderProperCoordinateSearch.rankWidth]
  have HRValue : Nat.fromBitsLE rwrd=rank:=FixedWidthNatVector.fromBitsLE_ofFn_testBit _ _ HBound
  obtain ⟨ordinary,mean,HOL,HML,HO,HMV,HFields⟩:=exists_own_words z hv hr
  let u:=FormulaSignSlotRadialProviderProperRowWitness.packet z ordinary mean rwrd
  have HKey : FormulaSignSlotRadialProviderProperRowWitness.key u=z:=by
    simp only [u,FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.key,pairFst_pair]
  have HAtomic : FormulaSignSlotRadialProviderProperRowWitness.atomic u=atomic z:=by
    rw [FormulaSignSlotRadialProviderProperRowWitness.atomic,HKey]
  have HValid : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u):=by
    rw [HAtomic];exact hv
  have HValues:=value_eq _ _ HAtomic HValid hv
  have HOw : FormulaSignSlotRadialProviderProperRowWitness.ownWord false u=ordinary:=by
    simp only [u,FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false]
  have HMw : FormulaSignSlotRadialProviderProperRowWitness.ownWord true u=mean:=by
    simp only [u,FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,ite_true]
  have HRw : FormulaSignSlotRadialProviderProperRowWitness.rank u=rwrd:=by
    simp only [u,FormulaSignSlotRadialProviderProperRowWitness.packet,FormulaSignSlotRadialProviderProperRowWitness.rank,pairSnd_pair]
  have HGood : FormulaSignSlotRadialProviderProperRowWitness.RowGood (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    rw [HKey];exact hr
  have HO' : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u):=by
    rw [HKey,HOw]
    exact (valid_at_context false z ordinary).mpr HO
  have HM' : SquareSampleCompleteVertices.Valid (Input (terminal true) (positive true))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u):=by
    rw [HKey,HMw]
    exact (valid_at_context true z mean).mpr HMV
  have HChild : pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    rw [HKey];exact (row_producer_bounds z hv hd hr).1
  have HMid : pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    rw [HKey];exact (row_producer_bounds z hv hd hr).2
  have HData : RowSemantics right z (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) HValid) rwrd:=by
    unfold RowSemantics
    refine ⟨φ,?_,?_,?_,?_⟩
    · simpa only [HValues] using Hφ
    · simpa only [HValues,HRValue,rank,meanValue,midValue,coord,old] using HNear
    · simpa only [HValues,meanValue,midValue,coord,old] using HMem
    · simpa only [HValues,rank,meanValue,midValue,coord,old] using HRValue
  have HData':=Eq.mp (congrArg (fun key=>RowSemantics right key
    (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) HValid) rwrd) HKey.symm) HData
  unfold RowSemantics at HData'
  obtain ⟨ψ,Hψ,HN,HMRoot,HCode⟩:=HData'
  have HNearFactory:=probe_near_of_semantics u right HValid HGood (HFields rwrd).1 HO' HChild
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at HNearFactory
  have HOrd:=HNearFactory ψ Hψ (by simpa only [HKey,HValues] using hab) (by simpa only [HRw] using HN)
  have HMeanFactory:=probe_rank_of_semantics u HValid HGood (HFields rwrd).2 HM' HMid
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at HMeanFactory
  have HMean:=HMeanFactory ψ Hψ HMRoot (by simpa only [HRw] using HCode)
  have HSide : FormulaSignSlotRadialProviderProperRowWitness.SideGood right (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    rw [HKey];exact hs
  have HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right:=
    ⟨HGood,HSide,HOrd,HMean,(HFields rwrd).1,(HFields rwrd).2⟩
  exact ⟨rwrd,HRLen,ordinary,HOL,mean,HML,HL⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
