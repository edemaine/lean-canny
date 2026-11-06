/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeWords
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowQuotients
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarPoint
/-! # Fresh probe field matches determine the actual native statistic values

These readbacks do not assume Near or Rank acceptance while constructing it.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "I"=>IntegralFramedPhysicalSquare.input P D H L F C hs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

private theorem point_value_comp (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (J : IntegralMixedFramedHistoryFamilyBits.Data Q E) (LL FF CC : List Bool→ℕ)
    (hh : IntegralMixedFramedStepHeight.FamilyInputs Q E LL FF CC)
    (k l : List Bool→List Bool)
    (hk : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (k c))
    (hl : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (l c))
    (f : List Bool→List Bool) (he : k=l∘f) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E J LL FF CC hh k hk) c w)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input Q E J LL FF CC hh l hl) (f c) w)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (k c)))
    (j : Fin ((IntegralMixedFramedHistoryFamilyBits.family Q E J).birth (l (f c))))
    (hij : i.val=j.val) :
    IntegralFramedPhysicalSquare.point Q E J LL FF CC hh k hk c w hv i=
      IntegralFramedPhysicalSquare.point Q E J LL FF CC hh l hl (f c) w hw j :=by
  subst k
  have HP : hk=(fun c=>hl (f c)):=Subsingleton.elim _ _
  subst hk
  have HI : i=j:=Fin.ext hij
  subst j
  exact congrFun (IntegralFramedPhysicalSquare.point_comp Q E J LL FF CC hh l hl f c w hv hw) i

theorem probe_own_scalar_value (mode : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (I (terminal mode) (positive mode)) z w)
    (p : ℕ) (hp : p<(G).birth (terminal mode z)) :
    IntegralFramedPhysicalSquare.point P D H L F C hs (terminal mode)
      (positive mode) z w hv ⟨(G).birth (terminal mode z)-1-p,by omega⟩=
      FormulaSignSlotRadialProviderFieldEquality.point (context mode z) w
        ((valid_at_context mode z w).mp hv) p :=by
  have HV:=(valid_at_context mode z w).mp hv
  have HP : p<FormulaSignSlotRadialProviderFieldEquality.count (context mode z):=by
    unfold FormulaSignSlotRadialProviderFieldEquality.count
    simpa only [terminal,Function.comp_apply] using hp
  have HF:=(FormulaSignSlotRadialProviderFieldEquality.point_env (context mode z) w HV p HP).trans
    (IntegralFramedPhysicalBankTerm.env_chronological B FormulaSignSlotRadialProviderRecordPlan.tables
      FormulaSignSlotRadialProviderAtomic.bank_represents (context mode z) w HV p HP)
  have HX:=point_value_comp P D H L F C hs (terminal mode) (B).key
    (positive mode) (B).positive (context mode) (by unfold terminal;rfl) z w hv HV
    ⟨(G).birth (terminal mode z)-1-p,by omega⟩
    ⟨(G).birth ((B).key (context mode z))-1-p,by
      change (G).birth ((B).key (context mode z))-1-p<FormulaSignSlotRadialProviderFieldEquality.count (context mode z)
      unfold FormulaSignSlotRadialProviderFieldEquality.count at *
      omega⟩ (by simp only [terminal,Function.comp_apply])
  exact HX.trans HF.symm

theorem probe_scalar_value (mean : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch mean u∈FormulaSignSlotRadialProviderFieldEqualityList.language)
    (hw : SquareSampleCompleteVertices.Valid (I (terminal mean) (positive mean))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u))
    (p : ℕ) (hp : p<creating (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (hfit : creating (FormulaSignSlotRadialProviderProperRowWitness.key u)≤
      (G).birth (terminal mean (FormulaSignSlotRadialProviderProperRowWitness.key u))) :
    IntegralFramedPhysicalSquare.point P D H L F C hs (terminal mean) (positive mean)
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw
      ⟨(G).birth (terminal mean (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-p,by omega⟩=
    originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv p :=by
  obtain ⟨hL,hR,HE⟩:=FormulaSignSlotRadialProviderProperRowWitness.fieldMatch_sound mean u HF
  have HEp : originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv p=
      FormulaSignSlotRadialProviderFieldEquality.point (context mean (FormulaSignSlotRadialProviderProperRowWitness.key u))
        (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) ((valid_at_context mean _ _).mp hw) p:=by
    simpa only [originalValue] using HE p hp
  exact (probe_own_scalar_value mean _ _ hw p (hp.trans_le hfit)).trans HEp.symm

private theorem same_root (mean : Bool) (z : List Bool) :
    pairFst (terminal mean z)=pairFst (parentKey mean z) :=by
  rw [parentKey_root]
  have HE:=FormulaSignSlotRadialProviderFieldEquality.key_root (context mean z)
  simpa only [terminal,Function.comp_apply,context,pairFst_pair] using HE

theorem probe_parent_values (mean : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HF : FormulaSignSlotRadialProviderProperRowWitness.fieldMatch mean u∈FormulaSignSlotRadialProviderFieldEqualityList.language)
    (hw : SquareSampleCompleteVertices.Valid (I (terminal mean) (positive mean))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u))
    (hfit : (G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal mean (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (φ : ((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : Interprets mean (FormulaSignSlotRadialProviderProperRowWitness.key u)
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw hfit φ) :
    ∀i : Fin ((G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))),
      φ (((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.numerator i)/
      (((G).state (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.denominator i:ℝ)=
      originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv
        ((G).birth (parentKey mean (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-i.val) :=by
  intro i
  let z:=FormulaSignSlotRadialProviderProperRowWitness.key u
  let old:=parentKey mean z
  have HB : (G).birth old=creating z:=parent_birth_actual mean z hv
  have HQ:=IntegralFramedPhysicalBankShift.values_of_interpretation P D H L F C hs
    (terminal mean) (positive mean) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw
    old (same_root mean z) hfit φ hφ i
  let p:=(G).birth old-1-i.val
  have HP : p<creating z:=by
    dsimp only [p,old,z]
    dsimp only [old,z] at HB
    have HI:=i.isLt
    omega
  have HFIT : creating z≤(G).birth (terminal mean z):=HB ▸ hfit
  have HV:=probe_scalar_value mean u hv HF hw p HP HFIT
  have HP0 : p<(G).birth (terminal mean z):=HP.trans_le HFIT
  have HE : embed hfit i=⟨(G).birth (terminal mean z)-1-p,by
      change (G).birth (terminal mean z)-1-p<(G).birth (terminal mean z)
      omega⟩:=by
    apply Fin.ext
    dsimp only [embed,Fin.val_mk,p,old,z]
    have HI:=i.isLt
    omega
  have HPoint:=congrArg (IntegralFramedPhysicalSquare.point P D H L F C hs
    (terminal mean) (positive mean) z (FormulaSignSlotRadialProviderProperRowWitness.ownWord mean u) hw) HE
  exact HQ.trans (HPoint.trans HV)

theorem probe_original_field_count (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context (atomic z))=
      creating z+1 :=by
  have HC:=row_count_positive z hv
  have HE:=FormulaSignSlotRadialProviderFieldEquality.count_eq (FormulaSignSlotRadialProviderAtomic.context (atomic z))
  simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair] at HE
  have HF : FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root (atomic z))=
      creating z+1:=by
    rw [FormulaSignSlotRadialProviderRecordPlan.fullCount,probe_old_count]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating initial FormulaSignSlotRadialProviderAtomic.initial
    omega
  simpa only [FormulaSignSlotRadialProviderAtomic.context] using HE.trans HF

theorem probe_field_list (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context mean z) w)
    (HE : ∀p<creating z,FormulaSignSlotRadialProviderFieldEquality.point (context mean z) w hw p=
      originalValue (atomic z) hv p) :
    FormulaSignSlotRadialProviderFieldEqualityList.packet
      (FormulaSignSlotRadialProviderAtomic.context (atomic z)) (FormulaSignSlotRadialProviderAtomic.word (atomic z))
      (context mean z) w (IntegralMixedRoadmapBadProbePacket.matchTable (initial z) (oldPacket z))∈
      FormulaSignSlotRadialProviderFieldEqualityList.language :=by
  let table:=IntegralMixedRoadmapBadProbePacket.matchTable (initial z) (oldPacket z)
  have HLabels (i : ℕ) (hi : i<WordListRecords.count table) :
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get table i)=i ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get table i)=i:=by
    have HI : i<creating z:=by
      simpa only [table,IntegralMixedRoadmapBadProbePacket.matchTable_count,creating] using hi
    rw [IntegralMixedRoadmapBadProbePacket.matchTable_lookup (initial z) (oldPacket z) i HI]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,and_self]
  have HL:=probe_original_field_count z hv
  have HR : FormulaSignSlotRadialProviderFieldEquality.count (context mean z)=creating z+1:=probe_full_count mean z hv
  have HB : ∀i<WordListRecords.count table,
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get table i)<
        FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context (atomic z)) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get table i)<
        FormulaSignSlotRadialProviderFieldEquality.count (context mean z):=by
    intro i hi
    rw [(HLabels i hi).1,(HLabels i hi).2,HL,HR]
    have HI : i<creating z:=by
      simpa only [table,IntegralMixedRoadmapBadProbePacket.matchTable_count,creating] using hi
    omega
  apply (FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff _ _ _ _ table
    (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) hw HB).mpr
  intro i hi
  rw [(HLabels i hi).1,(HLabels i hi).2]
  have HI : i<creating z:=by
    simpa only [table,IntegralMixedRoadmapBadProbePacket.matchTable_count,creating] using hi
  simpa only [originalValue] using (HE i HI).symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
