/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeFields
/-! # The natural reserved-parent readback equals the actual full-word field

The natural tuple is the zero extension of this word's actual joint tuple.
No equality of point maps, complete words or contexts is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial commands keyAt)
open IntegralMixedFramedRunObservation (ofCommands)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "H"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedExceptionalBounds.auxiliaryCap

def context (root : List Bool):=pair root []
def parent (n : List Bool→ℕ) (root : List Bool):=number n root+8+IntegralMixedCausalRecordPlanBits.count root-1

theorem rules_length (root : List Bool) :
    ((D).rules root).length=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root :=by
  rw [IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0,IntegralMixedCausalPlanBits.commands_length,
    IntegralMixedMarkedPrefixRecords.length]
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  omega

theorem bank_key (root : List Bool) :
    (B).key (context root)=keyAt root (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) [] :=by
  change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context root)=_
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,context,pairFst_pair]

private theorem prefix_congr (A : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan A)
    (r s : List Bool) (a b : ℕ) (hr : r=s) (hb : a=b) :
    HEq (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction A E r) (E.rules r) a)
      (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction A E s) (E.rules s) b) :=by
  cases hr
  cases hb
  rfl

theorem terminal_commands (root : List Bool) :HEq (commands P D ((B).key (context root))) ((D).rules root) :=by
  have HR :pairFst ((B).key (context root))=root :=by
    rw [bank_key hn ht ha hR0 root,IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  have HB :IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (context root))=((D).rules root).length :=by
    rw [bank_key hn ht ha hR0 root,IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ [] (by
      change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root≤
        IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root+2+1;omega),rules_length hn ht ha hR0]
  exact (prefix_congr P D _ root _ _ HR HB).trans (heq_of_eq (paddedPast_full _ _))

theorem room (root : List Bool) :((D).rules root).length≤(P).cap root+1+1 :=by
  rw [rules_length hn ht ha hR0]
  change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root≤
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root+2+1+1
  omega

noncomputable def fullObservation (root : List Bool) :=
  ofCommands (initial P D root) ((D).rules root) (room hn ht ha hR0 root)

private theorem commands_congr {a horizon width : ℕ} {Q : SpatialSource a} (x : State Q horizon width 0 (Fin 0))
    (cs ds : List (Instruction a width)) (hc : cs.length≤horizon+1) (hd : ds.length≤horizon+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd :=by cases he;rfl

private theorem root_commands_congr (A : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan A)
    (r s : List Bool) (cs : List (Instruction (A.ambient r) (A.width r)))
    (ds : List (Instruction (A.ambient s) (A.width s)))
    (hc : cs.length≤A.cap r+1+1) (hd : ds.length≤A.cap s+1+1)
    (hr : r=s) (he : HEq cs ds) :
    ofCommands (initial A E r) cs hc=ofCommands (initial A E s) ds hd :=by
  cases hr
  exact commands_congr _ _ _ _ _ (eq_of_heq he)

theorem terminal_data (root : List Bool) :
    ofCommands (initial P D (pairFst ((B).key (context root))))
      (commands P D ((B).key (context root)))
      (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))=
        fullObservation hn ht ha hR0 root :=by
  unfold fullObservation
  have HR :pairFst ((B).key (context root))=root :=by
    rw [bank_key hn ht ha hR0 root,IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  have HC:=terminal_commands hn ht ha hR0 root
  exact root_commands_congr P D _ root _ _ _ _ HR HC

theorem terminal_bank_data (root : List Bool) :
    ofCommands (initial (B).parameters (B).plan (pairFst ((B).key (context root))))
      (commands (B).parameters (B).plan ((B).key (context root)))
      (by rw [commands,paddedPast_length];exact (min_le_right _ _).trans (Nat.le_succ _))=
        fullObservation hn ht ha hR0 root :=terminal_data hn ht ha hR0 root

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable def natural (root w : List Bool) (hv : SquareSampleCompleteVertices.Valid S (context root) w) :=
  IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context root) w hv

theorem full_value (root w : List Bool) (hv : SquareSampleCompleteVertices.Valid S (context root) w)
    (i : ℕ) (hi : i<IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context root)) :
    (fullObservation hn ht ha hR0 root).point (natural hn ht ha hR0 root w hv) i=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0) (context root) w hv i :=by
  have HE:=IntegralFramedPhysicalPrefixPoint.full_point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context root) w hv ⟨i,hi⟩
  have HD:=congrArg (fun data=>data.point (natural hn ht ha hR0 root w hv) i)
    (terminal_bank_data hn ht ha hR0 root)
  refine HD.symm.trans (HE.trans ?_)
  unfold IntegralMixedPhysicalFieldEquality.pointNewest
  apply congrArg (IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive (context root) w hv)
  apply Fin.ext
  change i=min i (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context root)-1)
  exact (min_eq_left (by omega)).symm

theorem parent_data (root : List Bool) (hc : 0<IntegralMixedCausalRecordPlanBits.count root) :
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root
      (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)=
    ofCommands (initial P D root) (((D).rules root).drop 1) (by
      rw [List.length_drop];exact (Nat.sub_le _ _).trans (room hn ht ha hR0 root)) :=by
  unfold IntegralMixedMarkedPrefixObservation.observation
  apply commands_congr
  rw [paddedPast_valid _ _ _ (by rw [rules_length hn ht ha hR0 root];unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega)]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  rw [rules_length hn ht ha hR0 root]
  congr 1
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  omega

theorem parent_value (root w : List Bool) (hv : SquareSampleCompleteVertices.Valid S (context root) w)
    (hc : 0<IntegralMixedCausalRecordPlanBits.count root) (i : ℕ) (hi : i<parent n root) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root
      (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)).point
        (natural hn ht ha hR0 root w hv) i=
    IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha (radius_binary hR0) (context root) w hv (i+1) :=by
  rw [parent_data hn ht ha hR0 root hc]
  have HI :i<(((D).rules root).drop 1).length :=by
    rw [List.length_drop,rules_length hn ht ha hR0 root]
    exact hi
  refine (IntegralFramedPhysicalPrefixPoint.point_drop_one (initial P D root) ((D).rules root)
    (room hn ht ha hR0 root) _ _ ⟨i,HI⟩).trans ?_
  apply full_value hn ht ha hR0 root w hv (i+1)
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  unfold parent at hi
  omega

noncomputable def parentPoint (root w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (context root) w) :ℕ→ℝ :=
  (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root
    (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)).point
      (natural hn ht ha hR0 root w hv)

theorem parent_chronological (root w : List Bool) (hv : SquareSampleCompleteVertices.Valid S (context root) w)
    (hc : 0<IntegralMixedCausalRecordPlanBits.count root) (i : ℕ) (hi : i<parent n root) :
    parentPoint hn ht ha hR0 root w hv i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (context root) w hv (parent n root-1-i) :=by
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context root)=parent n root+1 :=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,parent]
    omega
  have HE :IntegralMixedPhysicalFieldEquality.newest
      (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (context root)) (parent n root-1-i)=i+1 :=by
    rw [HC]
    unfold IntegralMixedPhysicalFieldEquality.newest
    rw [min_eq_left (by omega)]
    omega
  unfold IntegralMixedPhysicalFieldEquality.point
  rw [HE]
  exact parent_value hn ht ha hR0 root w hv hc i hi

theorem packet_parent_iff (d initial : ℕ) (z w : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (pairFst z))
    (hi : initial=(B).parameters.ambient (IntegralMixedRoadmapBadProbePacket.root (pairFst z))+5)
    (hL : SquareSampleCompleteVertices.Valid S (context (IntegralMixedRoadmapBadProbePacket.root (pairFst z)))
      (IntegralMixedRoadmapBadProbePacket.word (pairFst z)))
    (hR' : SquareSampleCompleteVertices.Valid S (context (IntegralMixedRoadmapBadProbePacket.preparedRoot d z)) w) :
    IntegralMixedRoadmapBadProbeFields.packet d initial z w∈
        IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ↔
      ∀i<IntegralMixedRoadmapBadProbePacket.creating initial (pairFst z),
        parentPoint hn ht ha hR0 (IntegralMixedRoadmapBadProbePacket.root (pairFst z))
          (IntegralMixedRoadmapBadProbePacket.word (pairFst z)) hL i=
        parentPoint hn ht ha hR0 (IntegralMixedRoadmapBadProbePacket.preparedRoot d z) w hR' i :=by
  let l:=IntegralMixedRoadmapBadProbePacket.root (pairFst z)
  let r:=IntegralMixedRoadmapBadProbePacket.preparedRoot d z
  let m:=IntegralMixedRoadmapBadProbePacket.creating initial (pairFst z)
  have HCL :IntegralMixedCausalRecordPlanBits.count l=IntegralMixedRoadmapBadProbePacket.count (pairFst z) :=by
    simp only [l,IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapBadProbePacket.root,pairSnd_pair,pairFst_pair,IntegralMixedRoadmapBadProbePacket.count]
  have HCR :IntegralMixedCausalRecordPlanBits.count r=IntegralMixedRoadmapBadProbePacket.count (pairFst z) :=
    IntegralMixedRoadmapBadProbePacket.prepared_count d z hc
  have HIL :initial=number n l+8 :=hi.trans
    (IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z))
  have HPL :parent n l=m :=by
    unfold parent m IntegralMixedRoadmapBadProbePacket.creating
    rw [HCL,HIL]
  have HPR :parent n r=m :=by
    unfold parent
    rw [HCR,IntegralMixedRoadmapBadProbeFields.prepared_number (n:=n) d z]
    simpa only [parent,HCL] using HPL
  rw [IntegralMixedRoadmapBadProbeFields.packet_iff hn ht ha (radius_binary hR0) d initial z w hc hi hL hR']
  constructor
  · intro Hall i hi'
    have VL:=parent_chronological hn ht ha hR0 l _ hL (hc.trans_eq HCL.symm) i (hi'.trans_eq HPL.symm)
    have VR:=parent_chronological hn ht ha hR0 r _ hR' (hc.trans_eq HCR.symm) i (hi'.trans_eq HPR.symm)
    rw [HPL] at VL
    rw [HPR] at VR
    exact VL.trans ((Hall (m-1-i) (by omega)).trans VR.symm)
  · intro Hall i hi'
    have HJ :m-1-(m-1-i)=i :=by omega
    have VL:=parent_chronological hn ht ha hR0 l _ hL (hc.trans_eq HCL.symm) (m-1-i) (by omega)
    have VR:=parent_chronological hn ht ha hR0 r _ hR' (hc.trans_eq HCR.symm) (m-1-i) (by omega)
    rw [HPL,HJ] at VL
    rw [HPR,HJ] at VR
    exact VL.symm.trans ((Hall (m-1-i) (by omega)).trans VR)
end LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
