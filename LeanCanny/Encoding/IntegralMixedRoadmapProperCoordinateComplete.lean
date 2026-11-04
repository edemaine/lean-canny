/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankComplete
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNearComplete
public import LeanCanny.Encoding.IntegralMixedRoadmapRowMidpointPhysical
public import LeanCanny.Encoding.FixedWidthNatVector
/-! # A genuine geometric coordinate certificate has a bounded native witness -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def FamilyRootRank (F : IntegralMixedCutSource.Family) (k : List Bool)
    (φ : (F.state k).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (j : Fin (F.ambient k-(F.rule k).critical.offset.val+1)) (v : ℝ) : Prop:=
  v∈IntegralMixedFrozenFrameSectionCode.roots (F.state k) (F.birth_bound k) (F.rule k) φ t j ∧
    IntegralMixedSelectedRootRank.rank (F.state k) (F.birth_bound k) (F.rule k) φ t j v<2^F.width k

private theorem family_root_rank (F : IntegralMixedCutSource.Family) (k : List Bool)
    (φ : (F.state k).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (p : IntegralMixedSelectedPhysicalFiber.physical (F.state k) (F.birth_bound k) (F.rule k) φ t)
    (j : Fin (F.ambient k-(F.rule k).critical.offset.val+1)) :
    FamilyRootRank F k φ t j (p.val (ClearedCoordinateCritical.freeIndex (F.rule k).critical.offset.val (fit (F.rule k)).le j)):=by
  refine ⟨IntegralMixedFrozenFrameSectionCode.coordinate_mem (F.state k) (F.birth_bound k) (F.rule k) φ t p j,?_⟩
  have H:=IntegralMixedFrozenFrameSectionCode.ordinal_lt (F.state k) (F.birth_bound k) (F.rule k) φ t p j
  rw [IntegralMixedSelectedRootRank.ordinal_rank] at H
  exact H

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  parent terminal creating IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  parentKey root IntegralMixedCriticalSweep.selected IntegralMixedSelectedRootRank.rank
  IntegralMixedFrozenFrameSectionCode.roots IntegralMixedSelectedCoordinateEndpoint.Near
  IntegralMixedRoadmapLocalFrame.field originalValue
  FamilyRootRank

private def RowSemantics (right : Bool) (z : List Bool) (values : ℕ→ℝ) (rwrd : List Bool) : Prop:=
  let old:=parentKey hn ht ha hR0 false z
  let j:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z))
  let a:=(values (oldProducer false z)+values (oldProducer true z))/2
  ∃φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
      values ((G).birth old-1-i.val)) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near ((G).state old) ((G).birth_bound old) ((G).rule old) φ
      (values (oldProducer false z)) (values (oldProducer true z)) (values (oldProducer right z)) j
      (Nat.fromBitsLE rwrd) (values (pointProducer hn ht ha hR0 false z)) ∧
    values (pointProducer hn ht ha hR0 true z)∈IntegralMixedFrozenFrameSectionCode.roots
      ((G).state old) ((G).birth_bound old) ((G).rule old) φ a j ∧
    Nat.fromBitsLE rwrd=IntegralMixedSelectedRootRank.rank ((G).state old) ((G).birth_bound old) ((G).rule old) φ a j
      (values (pointProducer hn ht ha hR0 true z))

attribute [local irreducible] RowSemantics

private theorem original_field_eq (a b : List Bool) (he : a=b)
    (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) :
    originalValue hn ht ha hR0 a hA=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 b hB :=by
  subst b
  unfold originalValue IntegralMixedRoadmapLocalFrame.field
  rfl

/-- Both native statistic tests use one bounded rank word, while their
full sample words are independently constructed at their own prepared roots. -/
theorem holds_of_coordinate_meaning (right : Bool) (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (hj : IntegralMixedRoadmapAtomic.depth q≤j)
    (hjn : j≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (HM : CoordinateMeaning hn ht ha hR0 right q j hv) :
    IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right (pair q (BinaryNatCode.encode j)) :=by
  obtain ⟨HR,HSide,φ,Hφ,HNear⟩:=HM
  let z:=pair q (BinaryNatCode.encode j)
  have hz : atomic z=q:=pairFst_pair _ _
  have hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z):=by rw [hz];exact hv
  let old:=parentKey hn ht ha hR0 false z
  let coord:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z))
  let meanValue:=(IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
    IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2
  let midValue:=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
    (IntegralMixedRoadmapProper.midProducer (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q j)
  let rank:=IntegralMixedSelectedRootRank.rank ((G).state old) ((G).birth_bound old) ((G).rule old) φ meanValue coord midValue
  let r:=(G).rule old
  have HOffset : r.critical.offset.val=IntegralMixedRoadmapAtomic.depth q:=by
    have H:=rule_offset hn ht ha hR0 false z hA HR
    have HD:=HB.1
    simpa only [offset,hz,IntegralMixedRoadmapProper.levelIndex,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HD))] using H
  have HSelected : coord.val=j-IntegralMixedRoadmapAtomic.depth q:=by
    have H:=selected_coordinate hn ht ha hR0 false z hA HR
    have HD:=HB.1
    simpa only [coord,old,relativeCoordinate,coordinate,offset,hz,z,atomic,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      IntegralMixedRoadmapProper.levelIndex,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HD))] using H
  let ix : Fin ((G).ambient old+1):=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le coord
  have HIndex : ix.val=j:=by
    change r.critical.offset.val+coord.val=j
    exact (congrArg₂ Nat.add HOffset HSelected).trans (Nat.add_sub_of_le hj)
  have HPhysical:=IntegralMixedRoadmapLocalFrame.row_midpoint_physical hn ht ha hR0 q j hv HB HR φ Hφ
  let mid : IntegralMixedSelectedPhysicalFiber.physical ((G).state old) ((G).birth_bound old) r φ meanValue:=
    ⟨IntegralMixedRoadmapLocalFrame.rowMidpoint hn ht ha hR0 q j hv,HPhysical⟩
  have HPoint : mid.val ix=midValue:=by
    have H:=IntegralMixedRoadmapLocalFrame.row_midpoint_free hn ht ha hR0 q j hv HB ix (by rw [HIndex];exact hj)
    simpa only [HIndex] using H
  have HRaw:=family_root_rank G old φ meanValue mid coord
  have HNativeRoot:=Eq.mp (congrArg (fun v : ℝ=>FamilyRootRank G old φ meanValue coord v) HPoint) HRaw
  unfold FamilyRootRank at HNativeRoot
  have HMem:=HNativeRoot.1
  have HW : (G).width old=IntegralMixedRoadmapAtomic.width hn ht ha hR0 q:=by
    simpa only [hz] using IntegralMixedRoadmapLocalFrame.row_parent_width hn ht ha hR0 false z
  have HBound : rank<2^IntegralMixedRoadmapAtomic.width hn ht ha hR0 q:=
    HNativeRoot.2.trans_eq (congrArg (fun w : ℕ=>2^w) HW)
  have HRoot:=And.intro HMem HBound
  let rwrd:=List.ofFn (fun k : Fin (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q)=>rank.testBit k.val)
  have HRLen : rwrd.length=IntegralMixedRoadmapProperCoordinateSearch.rankWidth hn ht ha hR0 z:=by
    simp only [rwrd,List.length_ofFn,IntegralMixedRoadmapProperCoordinateSearch.rankWidth,hz]
  have HRValue : Nat.fromBitsLE rwrd=rank:=FixedWidthNatVector.fromBitsLE_ofFn_testBit _ _ HBound
  obtain ⟨ordinary,mean,HOL,HML,HO,HMV,HFields⟩:=exists_own_words hn ht ha hR0 z hA HR
  let u:=IntegralMixedRoadmapProperRowWitness.packet z ordinary mean rwrd
  have HKey : IntegralMixedRoadmapProperRowWitness.key u=z:=by
    simp only [u,IntegralMixedRoadmapProperRowWitness.packet,IntegralMixedRoadmapProperRowWitness.key,pairFst_pair]
  have HAtomic : IntegralMixedRoadmapProperRowWitness.atomic u=q:=by
    simpa only [IntegralMixedRoadmapProperRowWitness.atomic,HKey] using hz
  have HValid : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u):=by rw [HAtomic];exact hv
  have HValues:=original_field_eq hn ht ha hR0 _ _ HAtomic HValid hv
  have HOw : IntegralMixedRoadmapProperRowWitness.ownWord false u=ordinary:=by
    simp only [u,IntegralMixedRoadmapProperRowWitness.packet,IntegralMixedRoadmapProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false]
  have HMw : IntegralMixedRoadmapProperRowWitness.ownWord true u=mean:=by
    simp only [u,IntegralMixedRoadmapProperRowWitness.packet,IntegralMixedRoadmapProperRowWitness.ownWord,
      pairFst_pair,pairSnd_pair,ite_true]
  have HRw : IntegralMixedRoadmapProperRowWitness.rank u=rwrd:=by
    simp only [u,IntegralMixedRoadmapProperRowWitness.packet,IntegralMixedRoadmapProperRowWitness.rank,pairSnd_pair]
  have HGood : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by rw [HKey];exact HR
  have HO' : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u):=by
    rw [HKey,HOw];exact (valid_at_context hn ht ha hR0 false z ordinary).mpr HO
  have HM' : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord true u):=by
    rw [HKey,HMw];exact (valid_at_context hn ht ha hR0 true z mean).mpr HMV
  have HChild : pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    rw [HKey]
    simpa only [pointProducer,Bool.false_eq_true,ite_false,dimension,initial,atomic,coordinate,z,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using
      IntegralMixedRoadmapProper.child_producer_before_probe hn ht ha hR0 q hv j hj hjn
  have HMid : pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    rw [HKey]
    simpa only [pointProducer,ite_true,dimension,initial,atomic,coordinate,z,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using
      IntegralMixedRoadmapProper.mid_producer_before_probe hn ht ha hR0 q hv HB.1 j hj hjn
  have HData : RowSemantics hn ht ha hR0 right z
      (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) HValid) rwrd:=by
    unfold RowSemantics
    refine ⟨φ,?_,?_,?_,?_⟩
    · simpa only [HValues] using Hφ
    · simpa only [HValues,HRValue,rank,meanValue,midValue,coord,old,oldProducer,pointProducer,
        Bool.false_eq_true,ite_false,dimension,initial,coordinate,z,atomic,pairFst_pair,pairSnd_pair,
        BinaryNatCode.encode,Nat.fromBitsLE_bits] using HNear
    · simpa only [HValues,pointProducer,ite_true,dimension,initial,coordinate,z,atomic,pairFst_pair,pairSnd_pair,
        BinaryNatCode.encode,Nat.fromBitsLE_bits,oldProducer,meanValue,midValue,coord,old] using HRoot.1
    · simp only [HValues,HRValue,rank,meanValue,midValue,coord,old,oldProducer,pointProducer,
        ite_true,dimension,initial,coordinate,z,atomic,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HData' :=Eq.mp (congrArg (fun k=>RowSemantics hn ht ha hR0 right k
    (originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) HValid) rwrd) HKey.symm) HData
  unfold RowSemantics at HData'
  obtain ⟨ψ,Hψ,HN,HMRoot,HCode⟩:=HData'
  have HOrd:=probe_near_of_semantics hn ht ha hR0 u right HValid HGood (HFields rwrd).1 HO' HChild ψ Hψ
    (by simpa only [HKey,HValues,oldProducer,hz] using IntegralMixedRoadmapLocalFrame.order_of_base hn ht ha hR0 q hv HB)
    (by simpa only [HRw] using HN)
  have HMean:=probe_rank_of_semantics hn ht ha hR0 u HValid HGood (HFields rwrd).2 HM' HMid ψ Hψ HMRoot
    (by simpa only [HRw] using HCode)
  have HS : IntegralMixedRoadmapProperRowWitness.SideGood right (IntegralMixedRoadmapProperRowWitness.key u):=
    Eq.mp (congrArg (IntegralMixedRoadmapProperRowWitness.SideGood right) HKey.symm) HSide
  have HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right:=
    ⟨HGood,HS,HOrd,HMean,(HFields rwrd).1,(HFields rwrd).2⟩
  refine ⟨rwrd,HRLen,ordinary,HOL,mean,HML,?_⟩
  exact HL

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
