/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMidpointPoint
public import LeanCanny.Encoding.IntegralMixedRoadmapIdentityReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowFields
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepReadback
/-! # Actual MID and child points in the ordinary row's frozen frame -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
 (IntegralFramedBankQuery.Bank.parameters BK) (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.point

 IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalFieldEquality.point

def rowKey (q : List Bool):=pair q (BinaryNatCode.encode (IntegralMixedRoadmapAtomic.depth q))
noncomputable abbrev oldKey (q : List Bool):=IntegralMixedRoadmapProperRow.parentKey hn ht ha hR0 false (rowKey q)
noncomputable def ambient (q : List Bool):=(G).ambient (oldKey hn ht ha hR0 q)

theorem ambient_eq (q : List Bool) : ambient hn ht ha hR0 q=D q :=by
  simpa only [ambient,oldKey,rowKey,IntegralMixedRoadmapProperRow.parentDimension,
    IntegralMixedRoadmapProperRow.dimension,IntegralMixedRoadmapProperRow.atomic,pairFst_pair,
    IntegralMixedFramedHistoryFamilyBits.family] using
    IntegralMixedRoadmapProperRow.parentDimension_eq hn ht ha hR0 false (rowKey q)

noncomputable def midpoint (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    Fin (ambient hn ht ha hR0 q+1)→ℝ:=fun i=>IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) i)
noncomputable def child (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    Fin (ambient hn ht ha hR0 q+1)→ℝ:=fun i=>IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) i)

noncomputable def field (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (j : ℕ):=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) j

private theorem jet_transport {a b : ℕ} (P : SpatialSource a) (Q : SpatialSource b) (HD : a=b)
    (HS : HEq P Q) (p : Fin (a+1)→ℝ) (q : Fin (b+1)→ℝ) (HP : HEq p q) (k g : ℕ)
    (HZ : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (HG : ∀i : Fin (a+1),k ≤ i.val→i.val≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) q=0 ∧
    ∀i : Fin (b+1),k ≤ i.val→i.val≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂ (Int.castRingHom ℝ) q=0 :=by
  cases HD
  have H1 : P=Q:=eq_of_heq HS
  have H2 : p=q:=eq_of_heq HP
  simpa only [←H1,←H2] using And.intro HZ HG

private theorem cast_heq {a b : ℕ} (H : a=b) (p : Fin a→ℝ) :
    HEq p (fun i : Fin b=>p (Fin.cast H.symm i)) :=by cases H;rfl

theorem midpoint_source_rows (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q) :
    let P:=(G).spatial (oldKey hn ht ha hR0 q)
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) (midpoint hn ht ha hR0 q hv)=0 ∧
    ∀i : Fin (ambient hn ht ha hR0 q+1),IntegralMixedRoadmapAtomic.depth q ≤ i.val→i.val≠IntegralMixedRoadmapAtomic.depth q→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) (midpoint hn ht ha hR0 q hv)=0 :=by
  have hd:=HB.1
  have HA:=(IntegralMixedRoadmapProper.midpoint_sound hn ht ha hR0 q HB.2.2.1).choose_spec.1
  have HG:=IntegralMixedRoadmapProper.midpoint_context_good hn ht ha hR0 q hv hd
  have HF:=IntegralMixedPhysicalPointCompanionScan.midpoint_frame_point hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
    (IntegralMixedRoadmapProper.midBirth (D q) (N q) q) HA (IntegralMixedRoadmapProper.labels q)
    (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
    (IntegralMixedRoadmapProper.levelIndex q+1) (IntegralMixedRoadmapProper.levelIndex q+1) HG
    (IntegralMixedRoadmapProper.midpoint_context_command hn ht ha hR0 q hv hd)
  have HS:=IntegralMixedRoadmapProper.midpoint_source_original hn ht ha hR0 q hv hd
  have HT:=IntegralMixedPhysicalOriginalSource.family_source hn ht ha hR0 false (oldKey hn ht ha hR0 q)
  have HO : IntegralMixedAuxiliaryMarkedIntegerSource.original (pairFst (oldKey hn ht ha hR0 q))=
      IntegralMixedRoadmapAtomic.original q:=by
    rw [oldKey,IntegralMixedRoadmapProperRow.parentKey_root]
    simp only [IntegralMixedRoadmapProperRow.root,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair,IntegralMixedRoadmapAtomic.original,
      IntegralMixedRoadmapProperRow.atomic,rowKey]
  have HPsource:=HT.trans (IntegralMixedOriginalRegularSource.source_congr n t R0 _ _ HO)
  have HD : (BK).parameters.ambient (pairFst ((BK).key (IntegralMixedRoadmapAtomic.context q)))=
      ambient hn ht ha hR0 q :=
    (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q).trans (ambient_eq hn ht ha hR0 q).symm
  have HP : HEq (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapProper.midBirth (D q) (N q) q))
      (midpoint hn ht ha hR0 q hv):=by
    have H1:=cast_heq (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q))
      (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapProper.midBirth (D q) (N q) q))
    have H2:=cast_heq (congrArg (·+1) (ambient_eq hn ht ha hR0 q).symm)
      (IntegralMixedRoadmapProper.midpointPoint hn ht ha hR0 q hv)
    exact H1.trans H2
  apply jet_transport (IntegralMixedRoadmapProper.midpointSource hn ht ha hR0 q) _ HD
    (HS.trans HPsource.symm) _ _ HP (IntegralMixedRoadmapAtomic.depth q) (IntegralMixedRoadmapAtomic.depth q) HF.1
  intro i hi hne
  have HK : IntegralMixedRoadmapProper.levelIndex q+1=IntegralMixedRoadmapAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex;omega
  apply HF.2.2.2 i
  · rw [IntegralMixedRoadmapProper.labels_count,HK]
    exact hi
  · intro HE
    apply hne
    exact HE.trans HK



theorem child_frozen_labels (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : Fin (D q+1)) (hi : i.val<IntegralMixedRoadmapProper.levelIndex q) :
    IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv i=
      field hn ht ha hR0 q hv (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val)) :=by
  have HK : i.val<IntegralMixedRoadmapAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex at hi;omega
  have H:= (IntegralMixedRoadmapAtomic.occurrence hn ht ha hR0 q hv).frozen
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i) HK
  simpa only [IntegralMixedRoadmapIdentity.point,IntegralMixedRoadmapAtomic.levels,field,
    IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapChain.frozen_lookup _ _ _ HK,IntegralMixedRoadmapChain.frozen_lookup _ _ _ hi,
    Fin.val_cast] using H

theorem child_height (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : Fin (D q+1))
    (hi : i.val=IntegralMixedRoadmapProper.levelIndex q) :
    IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv i=
      if IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
      then field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)
      else field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q) :=by
  have HK : i.val<IntegralMixedRoadmapAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex at hi;omega
  have H:= (IntegralMixedRoadmapAtomic.occurrence hn ht ha hR0 q hv).frozen
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i) HK
  have HX : IntegralMixedRoadmapIdentity.point hn ht ha hR0 q hv i=
      IntegralMixedRoadmapAtomic.levels hn ht ha hR0 q hv i.val:=by
    simpa only [IntegralMixedRoadmapIdentity.point,Fin.val_cast] using H
  have HL : Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapAtomic.frozen q) i.val)=
      IntegralMixedRoadmapChain.chosen (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q):=by
    rw [IntegralMixedRoadmapAtomic.frozen,IntegralMixedRoadmapChain.frozen_lookup _ _ _ HK,hi]
  have HE : IntegralMixedRoadmapChain.chosen (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=
      if IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
      then IntegralMixedRoadmapProper.producer true q else IntegralMixedRoadmapProper.producer false q:=by
    by_cases HE : IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
    all_goals simp only [IntegralMixedRoadmapChain.chosen,IntegralMixedRoadmapProper.producer,
      HE,ite_true,ite_false,Bool.false_eq_true]
  rw [HX]
  unfold IntegralMixedRoadmapAtomic.levels
  rw [HL,HE]
  by_cases HE : IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
  all_goals simp only [HE,ite_true,ite_false,field]

attribute [local irreducible] rowKey midpoint child field
 IntegralMixedRoadmapAtomic.levels
 IntegralMixedRoadmapProperRow.parentKey IntegralMixedRoadmapProperRow.parentData

private theorem birth_eq (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) :
    (G).birth (oldKey hn ht ha hR0 q)=IntegralMixedRoadmapProperRow.parentBirth hn ht ha hR0 false (rowKey q) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth (BK).parameters (BK).plan (BK).data _).trans
    ((IntegralMixedRoadmapProperRow.parentKey_prefix hn ht ha hR0 false (rowKey q) HC).trans
      (IntegralMixedRoadmapProperRow.parentBirth_eq hn ht ha hR0 false (rowKey q) HC).symm)

attribute [local semireducible] IntegralMixedFramedHistoryFamilyBits.family

theorem midpoint_physical (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) :
    midpoint hn ht ha hR0 q hv∈IntegralMixedSelectedPhysicalFiber.physical ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ
      ((field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  have HG:= (IntegralMixedRoadmapProperRow.parent_good hn ht ha hR0 false (rowKey q) HC HR).1
  have Hbirth:=birth_eq hn ht ha hR0 q hv
  have Hfields:=midpoint_source_rows hn ht ha hR0 q hv HB
  have HRu:=IntegralMixedRoadmapProperRow.rule_at_parent hn ht ha hR0 false (rowKey q) HC HR
  rw [HRu]
  simp only [IntegralMixedRoadmapProperRow.parentData,Bool.false_eq_true,ite_false]
  apply IntegralMixedChronologicalSweepReadback.raw_physical ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _) _ Hbirth
    (IntegralMixedRoadmapProperRow.labels (rowKey q)) (IntegralMixedRoadmapProperRow.offset (rowKey q))
    (IntegralMixedRoadmapProperRow.coordinate (rowKey q)) HG φ
    (fun i=>field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) Hφ _ _ Hfields.1
  · intro i hi
    have HI : i<IntegralMixedRoadmapProper.levelIndex q:=by
      simpa only [IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,
        IntegralMixedRoadmapProper.labels_count] using hi
    have HH:=IntegralMixedRoadmapProper.midpointPoint_frozen hn ht ha hR0 q hv HB.1 HB.2.2.1
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) ⟨i,hi.trans_le HG.1.1⟩) HI
    have Hlabel : Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i)<
        (G).birth (oldKey hn ht ha hR0 q):=(HG.1.2 i hi).trans_eq Hbirth.symm
    have HE : (G).birth (oldKey hn ht ha hR0 q)-1-
        ((G).birth (oldKey hn ht ha hR0 q)-1-Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i))=
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i):=by omega
    change midpoint hn ht ha hR0 q hv ⟨i,hi.trans_le HG.1.1⟩=field hn ht ha hR0 q hv _
    rw [HE]
    simpa only [midpoint,field,IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,
      rowKey,pairFst_pair,Fin.val_cast] using HH
  · have HH:=IntegralMixedRoadmapProper.midpointPoint_height hn ht ha hR0 q hv HB.1 HB.2.2.1
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q))
        ⟨WordListRecords.count (IntegralMixedRoadmapProperRow.labels (rowKey q)),by
          have H1:=HG.2.1;have H2:=HG.2.2.1
          have HA : ambient hn ht ha hR0 q=IntegralMixedRoadmapProperRow.parentDimension hn ht ha hR0 false (rowKey q):=rfl
          rw [HA];omega⟩)
      (by simp only [Fin.val_cast,IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,
        rowKey,pairFst_pair,IntegralMixedRoadmapProper.labels_count])
    simpa only [midpoint,field] using HH
  · intro i hi hne
    apply Hfields.2 i
    · simpa only [IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,
        IntegralMixedRoadmapProper.labels_count,IntegralMixedRoadmapProper.levelIndex,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HB.1))] using hi
    · simpa only [IntegralMixedRoadmapProperRow.offset,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,
        IntegralMixedRoadmapProper.levelIndex,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt HB.1))] using hne


theorem child_frozen (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (φ : ((G).state (oldKey hn ht ha hR0 q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (Hφ : ∀i,φ (((G).state (oldKey hn ht ha hR0 q)).bank.numerator i)/
      (((G).state (oldKey hn ht ha hR0 q)).bank.denominator i:ℝ)=
        field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) :
    IntegralMixedSelectedCoordinateEndpoint.Frozen ((G).state (oldKey hn ht ha hR0 q))
      ((G).birth_bound _) ((G).rule (oldKey hn ht ha hR0 q)) φ
      (if IntegralMixedRoadmapChain.sideWord (IntegralMixedRoadmapAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
       then field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)
       else field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)) (child hn ht ha hR0 q hv) :=by
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic (rowKey q)):=by
    simpa only [rowKey,IntegralMixedRoadmapProperRow.atomic,pairFst_pair] using hv
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (rowKey q) HV
  have HG:=(IntegralMixedRoadmapProperRow.parent_good hn ht ha hR0 false (rowKey q) HC HR).1
  have Hbirth:=birth_eq hn ht ha hR0 q hv
  have HRu:=IntegralMixedRoadmapProperRow.rule_at_parent hn ht ha hR0 false (rowKey q) HC HR
  rw [HRu]
  simp only [IntegralMixedRoadmapProperRow.parentData,Bool.false_eq_true,ite_false]
  apply IntegralMixedChronologicalSweepReadback.raw_frozen ((G).state (oldKey hn ht ha hR0 q)) ((G).birth_bound _) _ Hbirth
    (IntegralMixedRoadmapProperRow.labels (rowKey q)) (IntegralMixedRoadmapProperRow.offset (rowKey q))
    (IntegralMixedRoadmapProperRow.coordinate (rowKey q)) HG φ
    (fun i=>field hn ht ha hR0 q hv ((G).birth (oldKey hn ht ha hR0 q)-1-i.val)) Hφ
  · intro i hi
    have HI : i<IntegralMixedRoadmapProper.levelIndex q:=by
      simpa only [IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,rowKey,pairFst_pair,
        IntegralMixedRoadmapProper.labels_count] using hi
    have HH:=child_frozen_labels hn ht ha hR0 q hv
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) ⟨i,hi.trans_le HG.1.1⟩) HI
    have Hlabel : Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i)<
        (G).birth (oldKey hn ht ha hR0 q):=(HG.1.2 i hi).trans_eq Hbirth.symm
    have HE : (G).birth (oldKey hn ht ha hR0 q)-1-
        ((G).birth (oldKey hn ht ha hR0 q)-1-Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i))=
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProperRow.labels (rowKey q)) i):=by omega
    change child hn ht ha hR0 q hv ⟨i,hi.trans_le HG.1.1⟩=field hn ht ha hR0 q hv _
    rw [HE]
    simpa only [child,field,IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,
      rowKey,pairFst_pair,Fin.val_cast] using HH
  · simpa only [child] using child_height hn ht ha hR0 q hv HB.1
      (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q))
        ⟨WordListRecords.count (IntegralMixedRoadmapProperRow.labels (rowKey q)),by
          have H1:=HG.2.1;have H2:=HG.2.2.1
          have HA : ambient hn ht ha hR0 q=IntegralMixedRoadmapProperRow.parentDimension hn ht ha hR0 false (rowKey q):=rfl
          rw [HA];omega⟩)
      (by simp only [Fin.val_cast,IntegralMixedRoadmapProperRow.labels,IntegralMixedRoadmapProperRow.atomic,
        rowKey,pairFst_pair,IntegralMixedRoadmapProper.labels_count])

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
