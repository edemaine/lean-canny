/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedFieldVertex
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParentMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCanonical
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape
/-! # A legal source-bounded hint has a fresh own word with all old fields -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbePreparedWord
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "wid"=>IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0)
variable (z : List Bool) (codes : List (List Bool)) (last : List Bool)
 (hraw :raw (pairFst z)=WordList.encode (codes++[last]))
local notation "new"=>preparedRoot (dim z) z
local notation "pk"=>IntegralMixedMarkedReservedVertex.parent (n:=n) (candidate (pairFst z)) codes (probe (dim z) z) []

include hraw in
theorem prepared_root :new=IntegralMixedMarkedPrefixRun.reservedRoot (candidate (pairFst z)) codes (probe (dim z) z) []:=by
 unfold preparedRoot preparedRaw IntegralMixedMarkedPrefixRun.reservedRoot
 rw [IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq (pairFst z) codes last hraw]

include hraw in
theorem parent_root :pairFst pk=new:=
 (IntegralMixedMarkedReservedVertex.parent_root (n:=n) _ _ _ _).trans
   (prepared_root hn ht ha hR0 z codes last hraw).symm

theorem prepared_ambient :(P).ambient new=dim z:=by
 change number n new+3=number n (root (pairFst z))+3
 rw [IntegralMixedRoadmapBadProbeFields.prepared_number]

include hraw in
theorem parent_ambient :(P).ambient (pairFst pk)=dim z:=by
 rw [parent_root hn ht ha hR0 z codes last hraw,prepared_ambient hn ht ha hR0 z]

include hraw in
theorem parent_birth :number n (pairFst pk)+8+codes.length=creating (ini z) (pairFst z):=by
 rw [parent_root hn ht ha hR0 z codes last hraw,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 rw [creating,HI,IntegralMixedRoadmapBadProbeCanonical.count_eq (pairFst z) codes last hraw]
 omega

private theorem point_congr (a b v : List Bool) (he :a=b)
    (hla :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context a) v)
    (hlb :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context b) v):
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 a v hla=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 b v hlb:=by cases he;rfl

include hraw in
theorem exists_fields
    (hh : HintGood (dim z) (ini z) (wid z) z)
    (hv :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
    (hd :Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).ambient+1)
      (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).source.degree):
    ∃w,∃hw:SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context new) w,
      ∀i<creating (ini z) (pairFst z),
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) hv i=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 new w hw i:=by
 have HN:=parent_ambient hn ht ha hR0 z codes last hraw
 have HM:=parent_birth hn ht ha hR0 z codes last hraw
 have HG :IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst pk))
     (number n (pairFst pk)+8+codes.length) (labels (pairFst z))
     (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)):=by
   rw [HN,HM]
   exact IntegralMixedRoadmapBadProbeShape.raw_good _ _ _ z hh
 let d:=IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst pk))
   (number n (pairFst pk)+8+codes.length) (labels (pairFst z)) _ _ HG
 have HC :probe (dim z) z=d.code (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
     (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z)):=by
   refine (congrArg (fun N : ℕ=>probe N z) HN).symm.trans ?_
   exact (IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ HG _ _ _
     (IntegralMixedRoadmapBadProbeShape.tag_le _ _ _ z hh)).symm
 have HP:=IntegralMixedRoadmapBadProbeParent.snapshot_prepared hn ht ha hR0 (dim z) z hh.1
 have HD:=hd.trans_eq (congrArg (fun A :IntegralMixedPrefixSnapshot.Data=>
   IntegralMixedExceptionalBounds.auxiliaryCap (A.ambient+1) A.source.degree) HP)
 rw [IntegralMixedRoadmapBadProbeParent.auxiliary_value hn ht ha hR0] at HD
 have HD' :Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient (pairFst pk)+1)
     (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 (pairFst pk)).degree:=by
   rw [parent_root hn ht ha hR0 z codes last hraw]
   exact HD
 have HR:=IntegralMixedRoadmapBadProbeCanonical.root_eq (pairFst z) codes last hraw
 have HV0 :SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
     (IntegralMixedMarkedReservedParent.context (root (pairFst z))) (word (pairFst z)):=
   (congrArg (fun I :SquareSampleInput.Inputs=>SquareSampleCompleteVertices.Valid I
     (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
       (IntegralMixedMarkedReservedPoint.input_eq hn ht ha hR0)).mpr hv
 have HV :SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
     (IntegralMixedMarkedReservedParent.context (IntegralMixedMarkedPrefixRun.reservedRoot (candidate (pairFst z)) codes last [])) (word (pairFst z)):=
   (congrArg (fun r=>SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
     (IntegralMixedMarkedReservedParent.context r) (word (pairFst z))) HR).mp HV0
 have VE:=IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0 (candidate (pairFst z)) codes last [] (word (pairFst z)) HV
 have VO :IntegralMixedMarkedReservedParent.values hn ht ha hR0 (candidate (pairFst z)) codes last [] (word (pairFst z)) HV=
     IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) hv:=
   VE.trans (point_congr hn ht ha hR0 _ _ _ HR.symm _ hv)
 obtain ⟨w,hw,HFields⟩:=IntegralMixedMarkedReservedFieldVertex.exists_parent_fields hn ht ha hR0 (candidate (pairFst z)) codes
   last [] (probe (dim z) z) [] (word (pairFst z)) HV d
   (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z))) (Nat.fromBitsLE (field 2 z))
   (Nat.fromBitsLE (field 3 z)) HD' HC
 have HEroot:=prepared_root hn ht ha hR0 z codes last hraw
 let F :List Bool→Prop:=fun r=>∃w,∃hw:SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context r) w,
   ∀i<creating (ini z) (pairFst z),IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z))
     (word (pairFst z)) hv i=IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 r w hw i
 apply (congrArg F HEroot.symm).mp
 refine ⟨w,hw,?_⟩
 intro i hi
 have HI :i<number n (IntegralMixedMarkedPrefixRun.reservedRoot (candidate (pairFst z)) codes (probe (dim z) z) [])+8+codes.length:=by
   have HM':=HM
   rw [IntegralMixedMarkedReservedVertex.parent_root (n:=n)] at HM'
   omega
 exact (congrFun VO i).symm.trans (HFields i HI).symm

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbePreparedWord
