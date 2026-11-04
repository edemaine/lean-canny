/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChild
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPastValues
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicOccurrence
/-! # The old accepted point is eligible for its own retained extension -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem observation_reframe {n S B :ℕ} {V :SpatialSource n}
    (x :IntegralMixedHistory.State V S B 0 (Fin 0))
    (cs :List (IntegralMixedFramedHistoryScript.Instruction n B)) (hc :cs.length≤S+1)
    (W :SpatialSource n) (hW :PurePowerReductionBounds.dimension (n+1) W.degree≤2^B)
    (z :ℕ→ℝ) (i :Fin cs.length) :
    (IntegralMixedFramedRunObservation.ofCommands x cs hc).point z i.val=
      IntegralMixedFullBankPoint.point
        (IntegralMixedHistory.reframe (IntegralMixedFramedHistoryScript.run x cs hc) W hW)
        (fun j=>z (IntegralMixedFramedPhysicalIndex.enumerate cs j).val) i :=by
  rw [IntegralMixedFramedRunObservation.point_actual]
  rfl

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
local notation "DIM"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot start
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.point
  IntegralMixedMarkedPrefixObservation.observation IntegralMixedPhysicalFieldEquality.point
  parentCommands parentState parentTuple parentValues
  IntegralMixedMarkedReservedParent.bank IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerPlan.degree
  IntegralMixedFramedHistoryScript.Index

theorem parent_value_old_field (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<DIM old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old)
    (i : Fin (parentCommands hn ht ha hR0 old hv hd e he).length) :
    parentValues hn ht ha hR0 old hv hd e he i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv)
        ((parentCommands hn ht ha hR0 old hv hd e he).length-1-i.val) :=by
  let r:=preparedRoot hn ht ha hR0 old e
  let cs:=parentCommands hn ht ha hR0 old hv hd e he
  have HO:=parent_observation hn ht ha hR0 old hv hd e he
  have HFull : (IntegralMixedFramedRunObservation.ofCommands (initial P PLAN r) cs
      (parent_room hn ht ha hR0 old hv hd e he)).point (oldNatural hn ht ha hR0 old hv) i.val=
      parentValues hn ht ha hR0 old hv hd e he i :=by
    unfold parentValues parentState parentTuple
    exact observation_reframe (initial P PLAN r) cs (parent_room hn ht ha hR0 old hv hd e he)
      (Q r) (IntegralMixedStaticRecordPrefix.cap (Q r)
        (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)) (oldNatural hn ht ha hR0 old hv) i
  have H0 : (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 r
      (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd e he)).point
        (oldNatural hn ht ha hR0 old hv) i.val=parentValues hn ht ha hR0 old hv hd e he i :=
    (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point (oldNatural hn ht ha hR0 old hv) i.val) HO).trans HFull
  apply H0.symm.trans
  have HRaw:=past_raw_native hn ht ha hR0 old hv hd e he (oldNatural hn ht ha hR0 old hv) (by intro j hj;rfl)
  have HN : number n (IntegralMixedRoadmapAtomic.root old)+8+start hn ht ha hR0 old=cs.length :=by
    rw [parent_length]
    unfold IntegralMixedRoadmapAtomic.endBirth
    have HI : IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old=number n (IntegralMixedRoadmapAtomic.root old)+8 :=by
      rw [IntegralMixedRoadmapAtomic.initial_eq]
      simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
        IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
        IntegralMixedRoadmapAtomic.original,pairFst_pair]
    rw [HI]
    unfold start
    rfl
  rw [past_prefix_point hn ht ha hR0 old hv hd e he _ _ HRaw _ le_rfl i.val (by rw [HN];exact i.isLt)]
  rw [chronological_value hn ht ha hR0 _ _ (old_valid_native hn ht ha hR0 old hv) _
    (start_fit hn ht ha hR0 old hv) i.val (by rw [HN];exact i.isLt),HN]
  rfl


theorem own_endpoint_fit (old : List Bool) :
    IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old<beginBirth hn ht ha hR0 old :=by
  unfold IntegralMixedRoadmapAtomic.ownBirth beginBirth IntegralMixedRoadmapAtomic.endBirth
    IntegralMixedRoadmapAtomic.initial
  omega

local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "E" old=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "ROOT" old=>preparedRoot hn ht ha hR0 old (E old)

theorem own_point_dimension (old : List Bool) : (P).ambient (ROOT old)=
    (BK).parameters.ambient (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context old))) :=
  (prepared_dimension hn ht ha hR0 old (E old)).trans
    (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 old).symm

noncomputable def ownPoint (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    Fin ((P).ambient (ROOT old)+1)→ℝ :=fun i=>
  IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv
    (Fin.cast (congrArg (·+1) (own_point_dimension hn ht ha hR0 old)) i)

private theorem cast_point_heq {a b :ℕ} (h :a=b) (p :Fin (b+1)→ℝ) :
    HEq (fun i :Fin (a+1)=>p (Fin.cast (congrArg (·+1) h) i)) p :=by cases h;rfl

theorem ownPoint_heq (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    HEq (ownPoint hn ht ha hR0 old hv) (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv) :=
  cast_point_heq (own_point_dimension hn ht ha hR0 old) _

theorem own_source_heq (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    HEq (IntegralMixedRoadmapAtomic.source hn ht ha hR0 old) (Q (ROOT old)) :=by
  have HQ :HEq (Q (ROOT old)) (IntegralMixedOriginalRegularSource.source n t R0
      (IntegralMixedRoadmapAtomic.original old)) :=by
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    apply IntegralMixedOriginalRegularSource.source_congr
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      preparedRoot,IntegralMixedRoadmapAtomic.root,candidate_packet,pairFst_pair,
      IntegralMixedRoadmapAtomic.original]
  exact (IntegralMixedRoadmapAtomic.source_original hn ht ha hR0 old hv).trans HQ.symm

private theorem occurrence_transport {a b k :ℕ} (V :SpatialSource a) (W :SpatialSource b)
    (hab :a=b) (hs :HEq V W) (levels :ℕ→ℝ) (p :Fin (a+1)→ℝ) (q :Fin (b+1)→ℝ)
    (hp :HEq p q) (h :IntegralMixedAtomicOccurrence.Occurrence V k levels p) :
    IntegralMixedAtomicOccurrence.Occurrence W k levels q :=by
  subst b
  cases eq_of_heq hs
  cases eq_of_heq hp
  exact h

theorem own_occurrence (old : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    IntegralMixedAtomicOccurrence.Occurrence (Q (ROOT old)) (IntegralMixedRoadmapAtomic.depth old)
      (IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv) (ownPoint hn ht ha hR0 old hv) :=
  occurrence_transport _ _ (own_point_dimension hn ht ha hR0 old).symm
    (own_source_heq hn ht ha hR0 old hv) _ _ _ (ownPoint_heq hn ht ha hR0 old hv).symm
    (IntegralMixedRoadmapAtomic.occurrence hn ht ha hR0 old hv)

private theorem reverse_reverse (b i :ℕ) (hi :i<b) :b-1-(b-1-i)=i :=by omega

private theorem reference_reverse {n b :ℕ} (d :IntegralMixedChronologicalFrame.Descriptor n b)
    (i :Fin d.labels.length) :b-1-(d.reference i).val=(d.labels.get i).val :=by
  change b-1-(b-1-(d.labels.get i).val)=(d.labels.get i).val
  exact reverse_reverse b _ (d.labels.get i).isLt

theorem parent_frozen_value (old : List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<DIM old) (e :ℕ) (he :e<beginBirth hn ht ha hR0 old)
    (i :Fin (parentDescriptor hn ht ha hR0 old hv hd e he).labels.length) :
    parentValues hn ht ha hR0 old hv hd e he
      ((parentDescriptor hn ht ha hR0 old hv hd e he).reference i)=
      IntegralMixedRoadmapAtomic.levels hn ht ha hR0 old hv i.val :=by
  let d:=parentDescriptor hn ht ha hR0 old hv hd e he
  have HL:=IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
  rw [parent_labels hn ht ha hR0 old hv hd e he] at HL
  have HE : (parentCommands hn ht ha hR0 old hv hd e he).length-1-(d.reference i).val=
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen old) i.val) :=
    (reference_reverse d i).trans HL.symm
  rw [parent_value_old_field,HE]
  rfl

theorem parent_endpoint_value (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<DIM old) (e :ℕ) (he :e<beginBirth hn ht ha hR0 old) :
    parentValues hn ht ha hR0 old hv hd e he
      (IntegralMixedChronologicalMidpoint.reference (endpointLabel hn ht ha hR0 old hv hd e he))=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) e :=by
  rw [parent_value_old_field]
  apply congrArg (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv))
  change (parentCommands hn ht ha hR0 old hv hd e he).length-1-
    ((parentCommands hn ht ha hR0 old hv hd e he).length-1-e)=e
  exact reverse_reverse _ e (he.trans_eq (parent_length hn ht ha hR0 old hv hd e he).symm)

attribute [local irreducible] IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedPhysicalPointCompanionScan.retained IntegralMixedPhysicalPointCompanionScan.selected

theorem own_height_field (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) (E old)=
    IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv
      ⟨IntegralMixedRoadmapAtomic.depth old,by
        rw [IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 old]
        exact Nat.lt_succ_of_le (IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 old hv)⟩ :=by
  have HB:=IntegralMixedRoadmapAtomic.own_active hn ht ha hR0 old hv
  have HS:=IntegralMixedPhysicalPointCompanionScan.selected_of_frame hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context old) (E old) (IntegralMixedRoadmapAtomic.frozen old)
    (IntegralMixedRoadmapAtomic.depth old) (IntegralMixedRoadmapAtomic.depth old)
    (IntegralMixedRoadmapAtomic.native_point_good hn ht ha hR0 old hv)
    (IntegralMixedRoadmapAtomic.native_creating_command hn ht ha hR0 old hv)
  obtain ⟨hw,HAll⟩:=(IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.root old) (IntegralMixedRoadmapAtomic.word old)).mp hv.2.2.2.2.1
  have H:=HAll (E old) (IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false _ _ HB).1 HB
  have HP : IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) (E old)=
      IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv :=by
    simpa only [IntegralMixedRoadmapAtomic.ownBirth] using
      IntegralMixedRoadmapAtomic.own_height_point hn ht ha hR0 old hv
  have HE :IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) (E old) HB=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) (E old)
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
          (IntegralMixedRoadmapAtomic.context old) (E old),
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ HB⟩ :=by
    simpa only [IntegralMixedPhysicalMarkedTest.sampleContext,IntegralMixedRoadmapAtomic.context] using H
  rw [HP] at HE
  apply (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) (E old) HB).symm.trans
  apply HE.trans
  apply congrArg (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
  exact Fin.ext HS


attribute [local irreducible] ownPoint parentDescriptor IntegralMixedRoadmapAtomic.levels

theorem own_point_eligible (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<DIM old) :
    let e:=E old
    let he:=own_endpoint_fit hn ht ha hR0 old
    let d:=parentDescriptor hn ht ha hR0 old hv hd e he
    let hk:=parent_descriptor_fit hn ht ha hR0 old hv hd e he
    let a:=endpointLabel hn ht ha hR0 old hv hd e he
    ownPoint hn ht ha hR0 old hv∈slice (Q (ROOT old)) d.frame (parentValues hn ht ha hR0 old hv hd e he) ∧
      ownPoint hn ht ha hR0 old hv (IntegralMixedChronologicalMidpoint.next d hk)=
        parentValues hn ht ha hR0 old hv hd e he (IntegralMixedChronologicalMidpoint.reference a) ∧
      ∀i,i∉(IntegralMixedChronologicalMidpoint.frame d hk a a).frozen→
        i≠(midpointObjective hn ht ha hR0 old hv hd e he).val→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial (Q (ROOT old)).low
          (Q (ROOT old)).leading (Q (ROOT old)).degree)).eval₂ (Int.castRingHom ℝ)
            (ownPoint hn ht ha hR0 old hv)=0 :=by
  dsimp only
  let e:=E old
  let he:=own_endpoint_fit hn ht ha hR0 old
  let d:=parentDescriptor hn ht ha hR0 old hv hd e he
  let hk:=parent_descriptor_fit hn ht ha hR0 old hv hd e he
  let a:=endpointLabel hn ht ha hR0 old hv hd e he
  have HO:=own_occurrence hn ht ha hR0 old hv
  have HL:=parent_descriptor_length hn ht ha hR0 old hv hd e he
  refine ⟨?_,?_,?_⟩
  · apply (d.slice_iff (Q (ROOT old)) (parentValues hn ht ha hR0 old hv hd e he)
      (ownPoint hn ht ha hR0 old hv)).mpr
    refine ⟨HO.zero,?_⟩
    intro i
    have HI :i.val<IntegralMixedRoadmapAtomic.depth old:=i.isLt.trans_eq HL
    have HF:=HO.frozen (⟨i.val,i.isLt.trans_le d.length_le⟩ :Fin ((P).ambient (ROOT old)+1)) HI
    exact HF.trans (parent_frozen_value hn ht ha hR0 old hv hd e he i).symm
  · rw [parent_endpoint_value hn ht ha hR0 old hv hd e he,own_height_field hn ht ha hR0 old hv]
    unfold ownPoint
    apply congrArg (IntegralMixedRoadmapAtomic.point hn ht ha hR0 old hv)
    apply Fin.ext
    exact HL
  · intro i hi _
    have HFree:=(IntegralMixedChronologicalMidpoint.free_iff d hk a a i).mp hi
    change (parentDescriptor hn ht ha hR0 old hv hd e he).labels.length+1 ≤ i.val at HFree
    rw [HL] at HFree
    exact HO.critical i (by omega) (by omega)

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
