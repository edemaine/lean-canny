/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch
public import LeanCanny.Encoding.IntegralMixedRoadmapProperInputComposition
public import LeanCanny.Encoding.IntegralMixedMarkedReservedFieldVertex
/-! # Actual ordinary and mean probes admit fresh own-root words

Only an accepted original node and its causal row grammar are used. The
reserved degree-zero cut is realized by padding zero, while every older
chronological quotient is retained. Near and rank acceptance are separate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedMarkedPrefixRun (reservedRoot)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def castData {a b n m :ℕ} (hn :a=n) (hm :b=m)
    (d :IntegralMixedCutRecordConstructor.Data n m) :IntegralMixedCutRecordConstructor.Data a b:=by
  cases hn
  cases hm
  exact d

private theorem castData_code {a b n m :ℕ} (hn :a=n) (hm :b=m)
    (d :IntegralMixedCutRecordConstructor.Data n m) (tag :IntegralMixedCausalRecordBits.Tag) (choice degree :ℕ) :
    (castData hn hm d).code tag choice degree=d.code tag choice degree:=by
  cases hn
  cases hm
  rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "BP"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family dimension initial creating parentDimension parentBirth parentData
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

private theorem old_count_positive (z :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z):=row_count_positive hn ht ha hR0 z hA

private theorem row_initial (z :List Bool) :
    number n (IntegralMixedRoadmapAtomic.root (atomic z))+8=initial hn ht ha hR0 z:=by
  rw [initial,IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,pairFst_pair,
    IntegralMixedRoadmapAtomic.original]

private theorem old_raw (z :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    ∃codes last,IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)=WordList.encode (codes++[last]):=
  IntegralMixedRoadmapLocalFrame.bad_raw_domain hn ht ha hR0 (atomic z) hA

private theorem base_root (z :List Bool) (codes :List (List Bool)) (last :List Bool)
    (hr :IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)=WordList.encode (codes++[last])) :
    IntegralMixedRoadmapAtomic.root (atomic z)=reservedRoot
      (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last []:=by
  have HE:=IntegralMixedRoadmapBadProbeCanonical.root_eq (oldPacket z) codes last hr
  have HB :IntegralMixedRoadmapAtomic.root (atomic z)=
      IntegralMixedRoadmapBadProbePacket.root (oldPacket z):=
    (IntegralMixedRoadmapProper.badPacket_root (atomic z)).symm
  have HF:=HB.trans HE
  simpa only [oldPacket,
    IntegralMixedRoadmapBadProbePacket.candidate,IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair] using HF

private theorem row_root (mean :Bool) (z :List Bool) (codes :List (List Bool)) (last :List Bool)
    (hr :IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)=WordList.encode (codes++[last])) :
    root hn ht ha hR0 mean z=reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z))
      codes (code hn ht ha hR0 mean z) []:=by
  rw [row_root_reserved,IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq _ codes last hr]

private theorem row_birth (mean :Bool) (z :List Bool) (codes :List (List Bool)) (last :List Bool)
    (hr :IntegralMixedRoadmapBadProbePacket.raw (oldPacket z)=WordList.encode (codes++[last])) :
    number n (root hn ht ha hR0 mean z)+8+codes.length=parentBirth hn ht ha hR0 mean z:=by
  rw [parentBirth,parentKey_root]
  rw [IntegralMixedRoadmapBadProbeCanonical.prefixCodes_eq _ codes last hr]

private theorem row_ambient (mean :Bool) (z :List Bool) :
    (BP).parameters.ambient (root hn ht ha hR0 mean z)=parentDimension hn ht ha hR0 mean z:=by
  have HE :BP=B:=by
    unfold IntegralMixedMarkedReservedParent.bank IntegralMixedPhysicalMarkedPlan.bank
    rfl
  rw [HE,root_dimension,parentDimension_eq]

private theorem exists_mode_parent (mean :Bool) (z :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (HR :IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w,
      ∀i<creating hn ht ha hR0 z,
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (root hn ht ha hR0 mean z) w hw i=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (IntegralMixedRoadmapAtomic.root (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA) i:=by
  obtain ⟨codes,last,hraw⟩:=old_raw hn ht ha hR0 z hA
  have HC:=old_count_positive hn ht ha hR0 z hA
  have HB:=base_root z codes last hraw
  have HRoot:=row_root hn ht ha hR0 mean z codes last hraw
  let pk:=IntegralMixedMarkedReservedVertex.parent (n:=n) (IntegralMixedRoadmapAtomic.candidate (atomic z))
    codes (code hn ht ha hR0 mean z) []
  have HK :pairFst pk=root hn ht ha hR0 mean z:=
    (IntegralMixedMarkedReservedVertex.parent_root (n:=n) _ _ _ _).trans HRoot.symm
  have HN :(BP).parameters.ambient (pairFst pk)=parentDimension hn ht ha hR0 mean z:=by
    rw [HK]
    exact row_ambient hn ht ha hR0 mean z
  have HM :number n (pairFst pk)+8+codes.length=parentBirth hn ht ha hR0 mean z:=by
    rw [HK]
    exact row_birth hn ht ha hR0 mean z codes last hraw
  let d:=castData HN HM (parentData hn ht ha hR0 mean z (parent_good hn ht ha hR0 mean z HC HR))
  have HD :(code hn ht ha hR0 mean z)=d.code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0:=by
    exact ((castData_code HN HM _ _ _ _).trans (parentData_code hn ht ha hR0 mean z _)).symm
  have HV :SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context
        (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last []))
      (IntegralMixedRoadmapAtomic.word (atomic z)):=by
    rw [IntegralMixedMarkedReservedPoint.input_eq hn ht ha hR0,←HB]
    exact IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA
  obtain ⟨w,hw,HP⟩:=IntegralMixedMarkedReservedFieldVertex.exists_parent_fields hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last [] (code hn ht ha hR0 mean z) []
    (IntegralMixedRoadmapAtomic.word (atomic z)) HV d (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0
    (Nat.zero_le _) HD
  have HO:=IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last [] (IntegralMixedRoadmapAtomic.word (atomic z)) HV
  have HE :creating hn ht ha hR0 z=number n (root hn ht ha hR0 mean z)+8+codes.length:=by
    rw [row_birth hn ht ha hR0 mean z codes last hraw,parentBirth_eq hn ht ha hR0 mean z HC]
  have HP' :∀i<creating hn ht ha hR0 z,
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes (code hn ht ha hR0 mean z) []) w hw i=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last [])
        (IntegralMixedRoadmapAtomic.word (atomic z)) (IntegralMixedMarkedReservedPoint.native_valid hn ht ha hR0 _ _ _ _ _ HV) i:=by
    intro i hi
    have HI :i<number n (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes
        (code hn ht ha hR0 mean z) [])+8+codes.length:=by rw [←HRoot,←HE];exact hi
    exact (HP i HI).trans (congrFun HO i)
  have HT : ∃w,∃hw :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context
      (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes (code hn ht ha hR0 mean z) [])) w,
    ∀i<creating hn ht ha hR0 z,
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes (code hn ht ha hR0 mean z) []) w hw i=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z)) codes last [])
        (IntegralMixedRoadmapAtomic.word (atomic z)) (IntegralMixedMarkedReservedPoint.native_valid hn ht ha hR0 _ _ _ _ _ HV) i:=⟨w,hw,HP'⟩
  simpa only [←HRoot,←HB,IntegralMixedMarkedPrefixFieldReadback.context,context] using HT

private theorem old_parent_birth (z :List Bool) :
    IntegralMixedMarkedPrefixFieldReadback.parent n (IntegralMixedRoadmapAtomic.root (atomic z))=
      creating hn ht ha hR0 z:=by
  rw [←IntegralMixedRoadmapLocalFrame.bad_parent_birth hn ht ha hR0 (atomic z),
    IntegralMixedRoadmapLocalFrame.bad_packet_initial hn ht ha hR0]
  rw [creating,initial,oldPacket]

private theorem new_parent_birth (mean :Bool) (z :List Bool)
    (HC :0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedMarkedPrefixFieldReadback.parent n (root hn ht ha hR0 mean z)=creating hn ht ha hR0 z:=by
  unfold IntegralMixedMarkedPrefixFieldReadback.parent
  rw [root_number,root_count hn ht ha hR0 mean z HC]
  rw [creating,IntegralMixedRoadmapBadProbePacket.creating]

private theorem old_field_count (z :List Bool)
    (HC :0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context (atomic z))=creating hn ht ha hR0 z+1:=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [IntegralMixedRoadmapAtomic.context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  rw [row_initial hn ht ha hR0 z,
    ←IntegralMixedRoadmapLocalFrame.bad_packet_count (atomic z)]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating oldPacket
  unfold oldPacket at HC
  omega

private theorem new_field_count (mean :Bool) (z :List Bool)
    (HC :0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (context hn ht ha hR0 mean z)=creating hn ht ha hR0 z+1:=by
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  rw [root_number,root_count hn ht ha hR0 mean z HC]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating
  omega

private theorem exists_mode_fields (mean :Bool) (z :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (HR :IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ∃w,∃hw :SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w,
      ∀j<creating hn ht ha hR0 z,
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
          (IntegralMixedRoadmapAtomic.context (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA) j=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
          (context hn ht ha hR0 mean z) w hw j:=by
  obtain ⟨w,hw,HP⟩:=exists_mode_parent hn ht ha hR0 mean z hA HR
  have HC:=old_count_positive hn ht ha hR0 z hA
  refine ⟨w,hw,fun j hj=>?_⟩
  let i:=creating hn ht ha hR0 z-1-j
  have HI :i<creating hn ht ha hR0 z:=by dsimp only [i];omega
  have HO:=IntegralMixedRoadmapLocalFrame.bad_parent_values hn ht ha hR0 (atomic z) hA i
    (by rw [old_parent_birth hn ht ha hR0 z];exact HI)
  have HN:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (root hn ht ha hR0 mean z) w hw (by rw [root_count hn ht ha hR0 mean z HC];exact HC) i
    (by rw [new_parent_birth hn ht ha hR0 mean z HC];exact HI)
  rw [old_parent_birth hn ht ha hR0 z] at HO
  rw [new_parent_birth hn ht ha hR0 mean z HC] at HN
  have HE :creating hn ht ha hR0 z-1-i=j:=by dsimp only [i];omega
  rw [HE] at HO HN
  unfold IntegralMixedRoadmapLocalFrame.field at HO
  exact HO.symm.trans ((HP i HI).symm.trans HN)

private theorem field_scan (mean :Bool) (z w :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hw :SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w)
    (HE :∀j<creating hn ht ha hR0 z,
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA) j=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (context hn ht ha hR0 mean z) w hw j) :
    IntegralMixedPhysicalFieldEqualityList.packet
      (IntegralMixedRoadmapAtomic.context (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
      (context hn ht ha hR0 mean z) w
      (IntegralMixedRoadmapBadProbePacket.matchTable (initial hn ht ha hR0 z) (oldPacket z))∈
        IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
  have HC:=old_count_positive hn ht ha hR0 z hA
  have HL (side :Bool) (i :ℕ) (hi :i<creating hn ht ha hR0 z) :
      IntegralMixedPhysicalFieldEqualityList.label side (WordList.get
        (IntegralMixedRoadmapBadProbePacket.matchTable (initial hn ht ha hR0 z) (oldPacket z)) i)=i:=by
    rw [creating] at hi
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup _ _ i hi]
    cases side <;> simp only [IntegralMixedPhysicalFieldEqualityList.label,
      Bool.false_eq_true,ite_false,ite_true,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  apply (IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha (radius_binary hR0)
    _ _ _ _ _ (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA) hw (by
      intro i hi
      rw [IntegralMixedRoadmapBadProbePacket.matchTable_count] at hi
      have hi :i<creating hn ht ha hR0 z:=by rw [creating];exact hi
      rw [HL false i hi,HL true i hi,old_field_count hn ht ha hR0 z HC,new_field_count hn ht ha hR0 mean z HC]
      exact ⟨by omega,by omega⟩)).mpr
  intro i hi
  rw [IntegralMixedRoadmapBadProbePacket.matchTable_count] at hi
  have hi :i<creating hn ht ha hR0 z:=by rw [creating];exact hi
  rw [HL false i hi,HL true i hi]
  exact HE i hi

theorem exists_own_words (z :List Bool)
    (hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (HR :IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ∃ordinary mean,
      ordinary.length=IntegralMixedRoadmapProperCoordinateSearch.fullWidth hn ht ha hR0 false z ∧
      mean.length=IntegralMixedRoadmapProperCoordinateSearch.fullWidth hn ht ha hR0 true z ∧
      SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 false z) ordinary ∧
      SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 true z) mean ∧
      ∀rank,IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 false
          (IntegralMixedRoadmapProperRowWitness.packet z ordinary mean rank)∈
          IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ∧
        IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 true
          (IntegralMixedRoadmapProperRowWitness.packet z ordinary mean rank)∈
          IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
  obtain ⟨ordinary,hO,HO⟩:=exists_mode_fields hn ht ha hR0 false z hA HR
  obtain ⟨mean,hM,HM⟩:=exists_mode_fields hn ht ha hR0 true z hA HR
  refine ⟨ordinary,mean,(Classical.choose hO).1,(Classical.choose hM).1,hO,hM,fun rank=>?_⟩
  have HS (mode :Bool) (w :List Bool) (hw :SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mode z) w)
      (HE :∀j<creating hn ht ha hR0 z,
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
          (IntegralMixedRoadmapAtomic.context (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 (atomic z) hA) j=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (context hn ht ha hR0 mode z) w hw j):=
    field_scan hn ht ha hR0 mode z w hA hw HE
  constructor
  · simpa only [IntegralMixedRoadmapProperRowWitness.fieldMatch,IntegralMixedRoadmapProperRowWitness.packet,
      IntegralMixedRoadmapProperRowWitness.atomic,IntegralMixedRoadmapProperRowWitness.key,
      IntegralMixedRoadmapProperRowWitness.ownWord,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,initial,oldPacket]
      using HS false ordinary hO HO
  · simpa only [IntegralMixedRoadmapProperRowWitness.fieldMatch,IntegralMixedRoadmapProperRowWitness.packet,
      IntegralMixedRoadmapProperRowWitness.atomic,IntegralMixedRoadmapProperRowWitness.key,
      IntegralMixedRoadmapProperRowWitness.ownWord,pairFst_pair,pairSnd_pair,ite_true,initial,oldPacket]
      using HS true mean hM HM

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
