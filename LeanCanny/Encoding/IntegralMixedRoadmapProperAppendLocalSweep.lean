/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperOriginalInterpretation
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowGood
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSelected
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepNumerical
public import LeanCanny.Geometry.IntegralMixedNumericalSweepNear
/-! # The actual coordinate probe has the canonical parent's numerical sweep -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem field_normalized_birth {a :ℕ} (r :Rule a) (values :ℕ→ℝ) (m k :ℕ) (he :m=k) (i :ℕ):
    IntegralMixedNumericalSweep.normalized r (fun j :Fin m=>values (m-1-j.val)) i=
      IntegralMixedNumericalSweep.normalized r (fun j :Fin k=>values (k-1-j.val)) i:=by
  subst k
  rfl

private theorem descriptor_atom_field {a m :ℕ} (w :List Bool)
    (H :IntegralMixedChronologicalFrameCode.Good a m w) (values :ℕ→ℝ)
    (i :Fin (a+1)) (hi :i.val<WordListRecords.count w):
    ((IntegralMixedChronologicalFrameCode.descriptor a m w H).atom i).value.evaluate
      (fun j :Fin m=>values (m-1-j.val))=values (Nat.fromBitsLE (WordList.get w i.val)):=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor a m w H
  have HI :i.val<d.labels.length:=hi.trans_eq
    (IntegralMixedChronologicalFrameCode.descriptor_length a m w H).symm
  have HL :(d.labels.get ⟨i.val,HI⟩).val=Nat.fromBitsLE (WordList.get w i.val):=
    (IntegralMixedChronologicalFrameCode.labels_lookup d i.val HI).symm.trans
      (IntegralMixedChronologicalFrameCode.descriptor_lookup a m w H i.val hi)
  change (d.atom i).value.evaluate (fun j :Fin m=>values (m-1-j.val))=_
  rw [Descriptor.atom,dite_eq_left HI]
  change (if h : (d.reference ⟨i.val,HI⟩).val<m then
    values (m-1-(⟨(d.reference ⟨i.val,HI⟩).val,h⟩ :Fin m).val) else 0)=_
  rw [dite_eq_left (d.reference ⟨i.val,HI⟩).isLt]
  apply congrArg values
  have HB:=(d.labels.get ⟨i.val,HI⟩).isLt
  change m-1-(m-1-(d.labels.get ⟨i.val,HI⟩).val)=_
  omega

private theorem raw_normalized_fields (a m :ℕ) (w :List Bool) (g j :ℕ)
    (H :IntegralMixedChronologicalCutCode.Good a m w g j) (Q :ℤ) (hQ :Q≠0)
    (values :ℕ→ℝ) (i :ℕ) (hi :i<WordListRecords.count w+1):
    IntegralMixedNumericalSweep.normalized
      ((IntegralMixedChronologicalCutCode.rawData a m w g j H).rule Q hQ)
      (fun k :Fin m=>values (m-1-k.val)) i=
      if i<WordListRecords.count w then C (values (Nat.fromBitsLE (WordList.get w i))) else X:=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor a m w H.1
  have HK:=IntegralMixedChronologicalCutCode.raw_fit a m w g j H
  have HL :d.labels.length=WordListRecords.count w:=
    IntegralMixedChronologicalFrameCode.descriptor_length a m w H.1
  have HI :i<a+1:=by have :=H.2.1;have :=H.2.2.1;omega
  let ix :Fin (a+1):=⟨i,HI⟩
  by_cases ho :i<WordListRecords.count w
  · have HH :(d.atom ix).value.evaluate (fun k :Fin m=>values (m-1-k.val))=
        values (Nat.fromBitsLE (WordList.get w i)):=descriptor_atom_field w H.1 values ix ho
    have HN:=data_normalized d HK _ _
      (IntegralMixedChronologicalCutCode.raw_free_g a m w g j H)
      (IntegralMixedChronologicalCutCode.raw_free_j a m w g j H) Q hQ
      (fun k :Fin m=>values (m-1-k.val)) ix
    have HE :¬ix.val=d.labels.length:=by dsimp only [ix];omega
    rw [HH] at HN
    simpa only [IntegralMixedChronologicalCutCode.rawData,ix,ite_eq_left ho,ite_eq_right HE,add_zero] using HN
  · have HE :i=d.labels.length:=by omega
    rw [ite_eq_right ho,HE]
    exact data_normalized_height d HK _ _
      (IntegralMixedChronologicalCutCode.raw_free_g a m w g j H)
      (IntegralMixedChronologicalCutCode.raw_free_j a m w g j H) Q hQ _

private theorem canonical_normalized_fields {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (d :Descriptor a m) (hk :d.labels.length<a+1)
    (g :Fin (a+1)) (hg :g∉(frame d hk).frozen) (values :Fin m→ℝ)
    (i :ℕ) (hi :i<d.labels.length+1):
    IntegralMixedNumericalSweep.normalized (cutRule x d.frame (next d hk) g hg) values i=
      if h :i<d.labels.length then C (values (d.reference ⟨i,h⟩)) else X:=by
  have HR:=data_rule x d hk g g hg hg
  have HE :IntegralMixedNumericalSweep.normalized
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) values i=
      IntegralMixedNumericalSweep.normalized (cutRule x d.frame (next d hk) g hg) values i:=
    (congrArg (fun r :Rule a=>IntegralMixedNumericalSweep.normalized r values i) HR).trans rfl
  rw [←HE]
  by_cases ho :i<d.labels.length
  · let ix :Fin (a+1):=⟨i,by omega⟩
    have HH :(d.atom ix).value.evaluate values=values (d.reference ⟨i,ho⟩):=by
      rw [Descriptor.atom,dite_eq_left ho]
      change (if h : (d.reference ⟨i,ho⟩).val<m then values ⟨(d.reference ⟨i,ho⟩).val,h⟩ else 0)=_
      rw [dite_eq_left (d.reference ⟨i,ho⟩).isLt]
    have HN:=data_normalized d hk g g hg hg (commonDenominator x) (commonDenominator_ne_zero x) values ix
    have HF :¬ix.val=d.labels.length:=by dsimp only [ix];omega
    rw [HH] at HN
    simpa only [ix,dite_eq_left ho,ite_eq_right HF,add_zero] using HN
  · have HF :i=d.labels.length:=by omega
    rw [dite_eq_right ho,HF]
    exact data_normalized_height d hk g g hg hg (commonDenominator x) (commonDenominator_ne_zero x) values

open IntegralMixedOriginalRegularSource (radius_binary)
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapLocalFrame.field IntegralMixedRoadmapProperRow.parentKey
  IntegralMixedRoadmapProperRow.parentData IntegralMixedRoadmapProperRow.parentDimension
  IntegralMixedRoadmapProperRow.parentBirth IntegralMixedRoadmapProperRow.creating

/-- The actual ordinary probe at the final original prefix has precisely the
same normalized frozen sweep as the earlier canonical geometric parent. -/
theorem WordReceipt.row_normalized {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (j :ℕ) (hj :IntegralMixedRoadmapAtomic.depth old+1≤j) (hjn :j≤D)
    (ell :ℕ) (hell :ell<IntegralMixedRoadmapAtomic.depth old+1):
    let q:=packet D old R.leftSpec R.rightSpec side W.word
    let key:=IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (pair q (BinaryNatCode.encode j))
    IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin ((G).birth key)=>IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV ((G).birth key-1-i.val)) ell=
    IntegralMixedNumericalSweep.normalized (cutRule x (d).frame (next d hk) g hg) V ell:=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  let z:=pair q (BinaryNatCode.encode j)
  let key:=IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false z
  let fields:=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV
  have hA :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z):=by
    simpa only [z,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hV
  have HD :0<IntegralMixedRoadmapAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HR:=IntegralMixedRoadmapProperRow.row_good_of_valid hn ht ha hR0 q hV HD j
    (by dsimp only [q];rw [depth_packet];exact hj) (by dsimp only [q];rw [dimension_packet];exact hjn)
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 z hA
  have HG:=IntegralMixedRoadmapProperRow.parent_good hn ht ha hR0 false z HC HR
  have HB :(G).birth key=IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false z:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth (BK).parameters (BK).plan (BK).data key).trans
      ((IntegralMixedRoadmapProperRow.parentKey_prefix hn ht ha hR0 false z HC).trans
        (IntegralMixedRoadmapProperRow.parentBirth_eq hn ht ha hR0 false z HC).symm)
  have HL :IntegralMixedRoadmapProperRow.labels z=IntegralMixedRoadmapAtomic.frozen old:=by
    simp only [IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,z,pairFst_pair]
    exact coarse_labels_packet hn ht ha hR0 old hv hd left right R side W.word
  have HData :IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin (IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false z)=>
        fields (IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false z-1-i.val)) ell=
      if ell<WordListRecords.count (IntegralMixedRoadmapProperRow.labels z) then
        C (fields (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels z) ell))) else X:=by
    rw [IntegralMixedRoadmapProperRow.rule_at_parent hn ht ha hR0 false z HC HR]
    simp only [IntegralMixedRoadmapProperRow.parentData,Bool.false_eq_true,ite_false]
    have HRaw:=raw_normalized_fields _ _ _ _ _ HG.1
      (commonDenominator ((G).state key)) (commonDenominator_ne_zero ((G).state key)) fields ell
      (by rw [HL,IntegralMixedRoadmapAtomic.frozen_count];exact hell)
    unfold IntegralMixedRoadmapProperRow.parentDimension at HRaw ⊢
    exact HRaw
  have HActual:IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val)) ell=
      if ell<IntegralMixedRoadmapAtomic.depth old then
        C (fields (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen old) ell))) else X:=by
    exact (field_normalized_birth ((G).rule key) fields _ _ HB ell).trans
      (by simpa only [HL,IntegralMixedRoadmapAtomic.frozen_count] using HData)
  have HLen:=(IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he)
  have HCanonical:=canonical_normalized_fields x d hk g hg V ell (by omega)
  apply HActual.trans
  apply Eq.trans ?_ HCanonical.symm
  by_cases hf :ell<(d).labels.length
  · have HO :ell<IntegralMixedRoadmapAtomic.depth old:=by omega
    rw [ite_eq_left HO,dite_eq_left hf]
    exact congrArg C (W.original_frozen_values hn ht ha hR0 old hv hd left right R side hV hOld ⟨ell,hf⟩)
  · have HO :¬ell<IntegralMixedRoadmapAtomic.depth old:=by omega
    rw [ite_eq_right HO,dite_eq_right hf]

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
