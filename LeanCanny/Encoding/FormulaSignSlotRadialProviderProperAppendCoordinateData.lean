/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperOriginalInterpretation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendFrozenValues
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepNormalized
/-! # Actual coordinate rules share the genuine canonical projection data -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem actual_bank_family :
    IntegralMixedFramedHistoryFamilyBits.family
      FormulaSignSlotRadialProviderRecordPlan.bank.parameters
      FormulaSignSlotRadialProviderRecordPlan.bank.plan
      FormulaSignSlotRadialProviderRecordPlan.bank.data=
    IntegralMixedFramedHistoryFamilyBits.family
      FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
      FormulaSignSlotRadialProviderRecordPlan.certifiedData :=rfl

private theorem renamed_source_refl {a :ℕ} (Q :SpatialSource a):
    IntegralMixedCoordinateRename.spatial Q (Equiv.refl _)=Q:=by
  cases Q
  simp only [IntegralMixedCoordinateRename.spatial,Equiv.refl_symm,Equiv.coe_refl,MvPolynomial.rename_id,AlgHom.id_apply]

private theorem raw_objective_zero (a m :ℕ) (labels :List Bool) (g j :ℕ)
    (H :IntegralMixedChronologicalCutCode.Good a m labels g j)
    (hg :g=WordListRecords.count labels+1) (Q :ℤ) (hQ :Q≠0):
    ((IntegralMixedChronologicalCutCode.rawData a m labels g j H).rule Q hQ).critical.objective=0:=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor a m labels H.1
  let hk:=IntegralMixedChronologicalCutCode.raw_fit a m labels g j H
  change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm ⟨g,H.2.2.1⟩).val-
    (frame d hk).frozen.card=0
  rw [(prefix_frozen d hk).permutation,frozen_card]
  have HL :d.labels.length=WordListRecords.count labels:=
    IntegralMixedChronologicalFrameCode.descriptor_length a m labels H.1
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  omega

private theorem plain_depth_eq (q : List Bool) : IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q :=rfl
private theorem family_ambient_value (p : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family p d h).ambient key=p.ambient (pairFst key) :=rfl
private theorem family_source_initial (p : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool)
    (Q : SpatialSource (p.ambient (pairFst key)))
    (hs : (IntegralMixedFramedHistoryFamilyBits.instruction p d key).source=d.initialSource (pairFst key))
    (hq : d.initialSource (pairFst key)=Q) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family p d h).spatial key) Q :=by
  exact heq_of_eq (hs.trans hq)

private theorem field_normalized_birth {a :ℕ} (r :Rule a) (values :ℕ→ℝ) (m k :ℕ) (he :m=k) (i :ℕ):
    IntegralMixedNumericalSweep.normalized r (fun j :Fin m=>values (m-1-j.val)) i=
      IntegralMixedNumericalSweep.normalized r (fun j :Fin k=>values (k-1-j.val)) i:=by
  subst k
  rfl

private theorem raw_normalized_fields (a m :ℕ) (w :List Bool) (g j :ℕ)
    (H :IntegralMixedChronologicalCutCode.Good a m w g j) (Q :ℤ) (hQ :Q≠0)
    (values :ℕ→ℝ) (i :ℕ) (hi :i<WordListRecords.count w+1):
    IntegralMixedNumericalSweep.normalized
      ((IntegralMixedChronologicalCutCode.rawData a m w g j H).rule Q hQ)
      (fun k :Fin m=>values (m-1-k.val)) i=
      if i<WordListRecords.count w then Polynomial.C (values (Nat.fromBitsLE (WordList.get w i))) else Polynomial.X:=by
  let d:=IntegralMixedChronologicalFrameCode.descriptor a m w H.1
  have HK:=IntegralMixedChronologicalCutCode.raw_fit a m w g j H
  have HL :d.labels.length=WordListRecords.count w:=
    IntegralMixedChronologicalFrameCode.descriptor_length a m w H.1
  have HN:=normalized_data d HK _ _
    (IntegralMixedChronologicalCutCode.raw_free_g a m w g j H)
    (IntegralMixedChronologicalCutCode.raw_free_j a m w g j H) Q hQ
    (fun k :Fin m=>values (m-1-k.val)) i (by omega)
  change IntegralMixedNumericalSweep.normalized ((data d HK _ _ _ _).rule Q hQ) _ i=_
  apply HN.trans
  by_cases hiw :i<WordListRecords.count w
  · have hid :i<d.labels.length:=by omega
    rw [dite_eq_left hid,ite_eq_left hiw]
    apply congrArg Polynomial.C
    apply congrArg values
    have HE :(d.labels.get ⟨i,hid⟩).val=Nat.fromBitsLE (WordList.get w i):=
      (IntegralMixedChronologicalFrameCode.labels_lookup d i hid).symm.trans
        (IntegralMixedChronologicalFrameCode.descriptor_lookup a m w H.1 i hiw)
    have HB:=(d.labels.get ⟨i,hid⟩).isLt
    change m-1-(m-1-(d.labels.get ⟨i,hid⟩).val)=_
    omega
  · have hid :¬i<d.labels.length:=by omega
    rw [dite_eq_right hid,ite_eq_right hiw]

private theorem canonical_normalized_fields {a S B m :ℕ} {P :SpatialSource a} {ι :Type}
    (x :State P S B m ι) (d :Descriptor a m) (hk :d.labels.length<a+1)
    (g :Fin (a+1)) (hg :g∉(frame d hk).frozen) (values :Fin m→ℝ)
    (i :ℕ) (hi :i<d.labels.length+1):
    IntegralMixedNumericalSweep.normalized (cutRule x d.frame (next d hk) g hg) values i=
      if h :i<d.labels.length then Polynomial.C (values (d.reference ⟨i,h⟩)) else Polynomial.X:=by
  have HR:=data_rule x d hk g g hg hg
  have HE :IntegralMixedNumericalSweep.normalized
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) values i=
      IntegralMixedNumericalSweep.normalized (cutRule x d.frame (next d hk) g hg) values i:=
    (congrArg (fun r :Rule a=>IntegralMixedNumericalSweep.normalized r values i) HR).trans rfl
  exact HE.symm.trans (normalized_data d hk g g hg hg _ _ values i hi)

variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "e"=>FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he"=>FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension old
local notation "d"=>FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk"=>FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "Q"=>FormulaSignSlotRadialProviderRecordPlan.spatial c
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters BK)
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
variable (left right :ParentEndpoint old hv hd)
  (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "packetW" w=>packet D old R.leftSpec R.rightSpec side w
local notation "keyW" w "," j=>FormulaSignSlotRadialProviderProperRow.parentKey false
  (pair (packetW w) (BinaryNatCode.encode j))
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderProperRow.parentKey FormulaSignSlotRadialProviderProperRow.parentDimension
  FormulaSignSlotRadialProviderProperRow.parentBirth FormulaSignSlotRadialProviderProperRow.parentData

theorem row_source (w : List Bool) (j : ℕ) :
    HEq ((G).spatial (keyW w, j))
      (IntegralMixedCoordinateRename.spatial Q (FrozenCoordinateOrdering.permutation (frame d hk).frozen)) :=by
  have HS : HEq ((G).spatial (keyW w, j))
      (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst (keyW w, j))):=by
    rw [actual_bank_family]
    exact family_source_initial P FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
      FormulaSignSlotRadialProviderRecordPlan.certifiedData (keyW w, j) _
      (FormulaSignSlotRadialProviderRecordPrefix.instruction_initial _)
      (FormulaSignSlotRadialProviderRecordPrefix.initial_source _)
  have HP : FormulaSignSlotRadialProviderRecordPlan.providerContext (pairFst (keyW w, j))=
      FormulaSignSlotRadialProviderRecordPlan.providerContext c:=by
    rw [FormulaSignSlotRadialProviderProperRow.parentKey_root,FormulaSignSlotRadialProviderProperRow.root_provider,
      FormulaSignSlotRadialProviderRetainedAppend.prepared_provider]
    simp only [FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair,provider_packet]
    exact (FormulaSignSlotRadialProviderAtomic.root_provider old).symm
  have HQ:=FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ HP
  have HR : IntegralMixedCoordinateRename.spatial Q (FrozenCoordinateOrdering.permutation (frame d hk).frozen)=Q:=by
    rw [(prefix_frozen d hk).permutation]
    exact renamed_source_refl Q
  exact HS.trans (HQ.trans (heq_of_eq HR.symm))

theorem row_ambient (w :List Bool) (j :ℕ):
    (G).ambient (keyW w, j)=(P).ambient c:=by
  have H:=FormulaSignSlotRadialProviderProperRow.parentDimension_eq false
    (pair (packetW w) (BinaryNatCode.encode j))
  have HE :(G).ambient (keyW w, j)=D:=by
    rw [family_ambient_value]
    simpa only [FormulaSignSlotRadialProviderProperRow.parentDimension,FormulaSignSlotRadialProviderProperRow.dimension,
      FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair,dimension_packet] using H
  exact HE.trans (FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e).symm

private theorem row_good (w :List Bool)
    (hV :FormulaSignSlotRadialProviderAtomic.Valid (packetW w))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    FormulaSignSlotRadialProviderProperRowWitness.RowGood (pair (packetW w) (BinaryNatCode.encode j)):=by
  apply FormulaSignSlotRadialProviderProperRow.row_good_of_valid _ hV
    (by rw [depth_packet];omega) j
  · rw [depth_packet]
    exact hj
  · rw [dimension_packet]
    exact hjn

theorem row_offset (w :List Bool)
    (hV :FormulaSignSlotRadialProviderAtomic.Valid (packetW w))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).critical.offset.val=FormulaSignSlotRadialProviderAtomic.depth old+1:=by
  have HA :FormulaSignSlotRadialProviderAtomic.Valid
      (FormulaSignSlotRadialProviderProperRow.atomic (pair (packetW w) (BinaryNatCode.encode j))):=by
    simpa only [FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hV
  have H:=FormulaSignSlotRadialProviderProperRow.rule_offset false _ HA
    (row_good old hv hd left right R side w hV j hj hjn)
  have HE :FormulaSignSlotRadialProviderProperRow.offset (pair (packetW w) (BinaryNatCode.encode j))=
      FormulaSignSlotRadialProviderAtomic.depth old+1:=by
    simp only [FormulaSignSlotRadialProviderProperRow.offset,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair,
      IntegralMixedRoadmapProper.levelIndex,plain_depth_eq,depth_packet]
    omega
  exact H.trans HE

theorem row_objective (w :List Bool)
    (hV :FormulaSignSlotRadialProviderAtomic.Valid (packetW w))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).critical.objective=0:=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic z):=by
    simpa only [z,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hV
  have HC:=FormulaSignSlotRadialProviderProperRow.row_count_positive z HA
  have HG:=row_good old hv hd left right R side w hV j hj hjn
  have HP:=FormulaSignSlotRadialProviderProperRow.parent_good false z HC HG
  rw [FormulaSignSlotRadialProviderProperRow.rule_at_parent false z HC HG]
  simp only [FormulaSignSlotRadialProviderProperRow.parentData,Bool.false_eq_true,ite_false]
  have HRaw:=raw_objective_zero _ _ _ _ _ HP.1 (FormulaSignSlotRadialProviderProperRow.offset_count z)
    (commonDenominator ((G).state (keyW w, j))) (commonDenominator_ne_zero ((G).state (keyW w, j)))
  unfold FormulaSignSlotRadialProviderProperRow.parentDimension at HRaw ⊢
  exact HRaw

theorem row_current (w :List Bool)
    (hV :FormulaSignSlotRadialProviderAtomic.Valid (packetW w))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    ((G).rule (keyW w, j)).slope=commonDenominator ((G).state (keyW w, j)):=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic z):=by
    simpa only [z,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hV
  exact FormulaSignSlotRadialProviderProperRow.rule_current false z
    (FormulaSignSlotRadialProviderProperRow.row_count_positive z HA)
    (row_good old hv hd left right R side w hV j hj hjn)

theorem row_coordinate (w :List Bool)
    (hV :FormulaSignSlotRadialProviderAtomic.Valid (packetW w))
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D):
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (keyW w, j)
      (get (BK).parameters Field.slot13 (FormulaSignSlotRadialProviderProperRow.parent false
        (pair (packetW w) (BinaryNatCode.encode j))))).val=j-(FormulaSignSlotRadialProviderAtomic.depth old+1):=by
  let z:=pair (packetW w) (BinaryNatCode.encode j)
  have HA :FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic z):=by
    simpa only [z,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using hV
  have H:=FormulaSignSlotRadialProviderProperRow.selected_coordinate false z HA
    (row_good old hv hd left right R side w hV j hj hjn)
  have HE :FormulaSignSlotRadialProviderProperRow.relativeCoordinate z=j-(FormulaSignSlotRadialProviderAtomic.depth old+1):=by
    simp only [z,FormulaSignSlotRadialProviderProperRow.relativeCoordinate,FormulaSignSlotRadialProviderProperRow.coordinate,
      FormulaSignSlotRadialProviderProperRow.offset,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedRoadmapProper.levelIndex,plain_depth_eq,depth_packet]
    omega
  exact H.trans HE

local notation "x"=>FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "V"=>FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd e he
local notation "g"=>FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg"=>FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he

/-- The actual ordinary probe at the final original prefix has precisely the
same normalized frozen sweep as the earlier canonical geometric parent. -/
theorem SampledLevel.row_normalized {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (S :SampledLevel old hv hd left right R side pMID pChild)
    (j :ℕ) (hj :FormulaSignSlotRadialProviderAtomic.depth old+1≤j) (hjn :j≤D)
    (ell :ℕ) (hell :ell<FormulaSignSlotRadialProviderAtomic.depth old+1):
    let q:=packet D old R.leftSpec R.rightSpec side S.receipt.word
    let key:=FormulaSignSlotRadialProviderProperRow.parentKey false (pair q (BinaryNatCode.encode j))
    IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin ((G).birth key)=>FormulaSignSlotRadialProviderAtomic.field q S.atomic_valid ((G).birth key-1-i.val)) ell=
    IntegralMixedNumericalSweep.normalized (cutRule x (d).frame (next d hk) g hg) V ell:=by
  let q:=packet D old R.leftSpec R.rightSpec side S.receipt.word
  let z:=pair q (BinaryNatCode.encode j)
  let key:=FormulaSignSlotRadialProviderProperRow.parentKey false z
  let fields:=FormulaSignSlotRadialProviderAtomic.field q S.atomic_valid
  have hA :FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRow.atomic z):=by
    simpa only [z,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair] using S.atomic_valid
  have HD :0<FormulaSignSlotRadialProviderAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  have HR:=FormulaSignSlotRadialProviderProperRow.row_good_of_valid q S.atomic_valid HD j
    (by dsimp only [q];rw [depth_packet];exact hj) (by dsimp only [q];rw [dimension_packet];exact hjn)
  have HC:=FormulaSignSlotRadialProviderProperRow.row_count_positive z hA
  have HG:=FormulaSignSlotRadialProviderProperRow.parent_good false z HC HR
  have HB :(G).birth key=FormulaSignSlotRadialProviderProperRow.parentBirth false z:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth (BK).parameters (BK).plan (BK).data key).trans
      ((FormulaSignSlotRadialProviderProperRow.parentKey_prefix false z HC).trans
        (FormulaSignSlotRadialProviderProperRow.parentBirth_eq false z HC).symm)
  have HL :FormulaSignSlotRadialProviderProperRow.labels z=FormulaSignSlotRadialProviderAtomic.frozen old:=by
    simp only [FormulaSignSlotRadialProviderProperRow.labels,FormulaSignSlotRadialProviderProperRow.atomic,z,pairFst_pair]
    exact coarse_labels_packet old hv hd left right R side S.receipt.word
  have HData :IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin (FormulaSignSlotRadialProviderProperRow.parentBirth false z)=>
        fields (FormulaSignSlotRadialProviderProperRow.parentBirth false z-1-i.val)) ell=
      if ell<WordListRecords.count (FormulaSignSlotRadialProviderProperRow.labels z) then
        Polynomial.C (fields (Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderProperRow.labels z) ell))) else Polynomial.X:=by
    rw [FormulaSignSlotRadialProviderProperRow.rule_at_parent false z HC HR]
    simp only [FormulaSignSlotRadialProviderProperRow.parentData,Bool.false_eq_true,ite_false]
    have HRaw:=raw_normalized_fields _ _ _ _ _ HG.1
      (commonDenominator ((G).state key)) (commonDenominator_ne_zero ((G).state key)) fields ell
      (by rw [HL,FormulaSignSlotRadialProviderAtomic.frozen_count];exact hell)
    unfold FormulaSignSlotRadialProviderProperRow.parentDimension at HRaw ⊢
    exact HRaw
  have HActual:IntegralMixedNumericalSweep.normalized ((G).rule key)
      (fun i :Fin ((G).birth key)=>fields ((G).birth key-1-i.val)) ell=
      if ell<FormulaSignSlotRadialProviderAtomic.depth old then
        Polynomial.C (fields (Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen old) ell))) else Polynomial.X:=by
    exact (field_normalized_birth ((G).rule key) fields _ _ HB ell).trans
      (by simpa only [HL,FormulaSignSlotRadialProviderAtomic.frozen_count] using HData)
  have HLen:=(FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he)
  have HCanonical:=canonical_normalized_fields x d hk g hg V ell (by omega)
  apply HActual.trans
  apply Eq.trans ?_ HCanonical.symm
  by_cases hf :ell<(d).labels.length
  · have HO :ell<FormulaSignSlotRadialProviderAtomic.depth old:=by omega
    rw [ite_eq_left HO,dite_eq_left hf]
    exact congrArg Polynomial.C (S.original_frozen_values ⟨ell,hf⟩)
  · have HO :¬ell<FormulaSignSlotRadialProviderAtomic.depth old:=by omega
    rw [ite_eq_right HO,dite_eq_right hf]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
