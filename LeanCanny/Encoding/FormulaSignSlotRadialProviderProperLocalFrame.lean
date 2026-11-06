/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointMembership
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentityReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperBase
/-! # Actual child and MID-anchor points in the provider ordinary-parent source -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family
  FormulaSignSlotRadialProviderRecordPlan.certifiedParameters FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
  FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
local notation "A"=>FormulaSignSlotRadialProviderAtomic.Valid
local notation "C"=>FormulaSignSlotRadialProviderAtomic.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.point

def rowKey (q :List Bool):=pair q (BinaryNatCode.encode (FormulaSignSlotRadialProviderAtomic.depth q))
noncomputable abbrev oldKey (q :List Bool):=FormulaSignSlotRadialProviderProperRow.parentKey false (rowKey q)
noncomputable def ambient (q :List Bool):=(G).ambient (oldKey q)

theorem ambient_eq (q :List Bool) :ambient q=D q:=by
  simpa only [ambient,oldKey,rowKey,FormulaSignSlotRadialProviderProperRow.parentDimension,
    FormulaSignSlotRadialProviderRecordPlan.bank,
    FormulaSignSlotRadialProviderProperRow.dimension,FormulaSignSlotRadialProviderProperRow.atomic,pairFst_pair,
    IntegralMixedFramedHistoryFamilyBits.family] using
    FormulaSignSlotRadialProviderProperRow.parentDimension_eq false (rowKey q)

theorem native_ambient_eq (q :List Bool) :
    (B).parameters.ambient (pairFst ((B).key (C q)))=ambient q:=
  (FormulaSignSlotRadialProviderAtomic.native_dimension q).trans (ambient_eq q).symm

noncomputable def midpoint (q :List Bool) (hv :A q) :Fin (ambient q+1)→ℝ:=fun i=>
  FormulaSignSlotRadialProviderAtomic.geometricPoint (C q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midBirth (D q) (N q) q)
    (Fin.cast (congrArg (·+1) (native_ambient_eq q)).symm i)

noncomputable def child (q :List Bool) (hv :A q) :Fin (ambient q+1)→ℝ:=fun i=>
  FormulaSignSlotRadialProviderIdentity.point q hv (Fin.cast (congrArg (·+1) (ambient_eq q)) i)
noncomputable def field (q :List Bool) (hv :A q) (i :ℕ):=FormulaSignSlotRadialProviderAtomic.field q hv i

private theorem raw_depth (q :List Bool) :IntegralMixedRoadmapAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth q:=rfl
private theorem raw_payload (q :List Bool) :IntegralMixedRoadmapAtomic.payload q=FormulaSignSlotRadialProviderAtomic.payload q:=rfl
private theorem raw_first (n initial :ℕ) (q :List Bool) :IntegralMixedRoadmapAtomic.first n initial q=FormulaSignSlotRadialProviderAtomic.first n initial q:=rfl

private theorem midpoint_packet (q :List Bool) (n initial :ℕ) :
    midCompanions n initial q=pair (pair (C q) (FormulaSignSlotRadialProviderAtomic.word q))
      (IntegralMixedPhysicalPointCompanionScan.descriptor (midBirth n initial q) (midFirst n initial q) (captureCount n q)):=rfl

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderProper.Base FormulaSignSlotRadialProviderProper.Midpoint
  FormulaSignSlotRadialProviderAtomic.Companions.language
  IntegralFramedPhysicalCompanionPoint.geometricPoint
  FormulaSignSlotRadialProviderProperRow.midpointRowCapture midpoint child field

private theorem base_depth (q :List Bool) (HB :FormulaSignSlotRadialProviderProper.Base q) :
    0<FormulaSignSlotRadialProviderAtomic.depth q:=by
  unfold FormulaSignSlotRadialProviderProper.Base at HB
  exact HB.1

theorem midpoint_capture_eq (q :List Bool) (hv :A q) (HB :FormulaSignSlotRadialProviderProper.Base q)
    (i :ℕ) (hi :i<captureCount (D q) q) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C q) (FormulaSignSlotRadialProviderAtomic.word q)
      (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midFirst (D q) (N q) q+i)=
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C q) (FormulaSignSlotRadialProviderAtomic.word q)
      (FormulaSignSlotRadialProviderAtomic.full_valid q hv) (midBirth (D q) (N q) q):=by
  have HMid:=HB
  unfold FormulaSignSlotRadialProviderProper.Base at HMid
  have HMP:=HMid.2.2.1
  unfold FormulaSignSlotRadialProviderProper.Midpoint at HMP
  rw [midpoint_packet] at HMP
  have HA:=FormulaSignSlotRadialProviderAtomic.anchor_active_packet (C q)
    (FormulaSignSlotRadialProviderAtomic.word q) _ _ _ HMP
  unfold FormulaSignSlotRadialProviderAtomic.Companions.language at HMP
  exact ((FormulaSignSlotRadialProviderAtomic.holds_iff_points (C q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
    _ _ _ HA).mp HMP.2.2 i hi).choose_spec.1

theorem child_frozen_labels (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : Fin (D q+1)) (hi : i.val<IntegralMixedRoadmapProper.levelIndex q) :
    FormulaSignSlotRadialProviderIdentity.point q hv i=
      field q hv (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val)) :=by
  have HK : i.val<FormulaSignSlotRadialProviderAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex at hi;simp only [raw_depth] at hi;omega
  have H:= (FormulaSignSlotRadialProviderAtomic.occurrence q hv).frozen
    (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm i) HK
  simpa only [FormulaSignSlotRadialProviderIdentity.point,FormulaSignSlotRadialProviderAtomic.levels,field,
    FormulaSignSlotRadialProviderAtomic.frozen,IntegralMixedRoadmapProper.labels,
    IntegralMixedRoadmapChain.frozen_lookup _ _ _ HK,IntegralMixedRoadmapChain.frozen_lookup _ _ _ hi,
    raw_payload,Fin.val_cast] using H

theorem child_height (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : Fin (D q+1))
    (hi : i.val=IntegralMixedRoadmapProper.levelIndex q) :
    FormulaSignSlotRadialProviderIdentity.point q hv i=
      if IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
      then field q hv (IntegralMixedRoadmapProper.producer true q)
      else field q hv (IntegralMixedRoadmapProper.producer false q) :=by
  have HK : i.val<FormulaSignSlotRadialProviderAtomic.depth q:=by
    unfold IntegralMixedRoadmapProper.levelIndex at hi;simp only [raw_depth] at hi;omega
  have H:= (FormulaSignSlotRadialProviderAtomic.occurrence q hv).frozen
    (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm i) HK
  have HX : FormulaSignSlotRadialProviderIdentity.point q hv i=
      FormulaSignSlotRadialProviderAtomic.levels q hv i.val:=by
    simpa only [FormulaSignSlotRadialProviderIdentity.point,Fin.val_cast] using H
  have HL : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)=
      IntegralMixedRoadmapChain.chosen (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q):=by
    rw [FormulaSignSlotRadialProviderAtomic.frozen,IntegralMixedRoadmapChain.frozen_lookup _ _ _ HK,hi]
  have HE : IntegralMixedRoadmapChain.chosen (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=
      if IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
      then IntegralMixedRoadmapProper.producer true q else IntegralMixedRoadmapProper.producer false q:=by
    by_cases HE : IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
    all_goals simp only [IntegralMixedRoadmapChain.chosen,IntegralMixedRoadmapProper.producer,
      HE,ite_true,ite_false,Bool.false_eq_true,raw_payload]
  rw [HX]
  unfold FormulaSignSlotRadialProviderAtomic.levels
  rw [HL,HE]
  by_cases HE : IntegralMixedRoadmapChain.sideWord (FormulaSignSlotRadialProviderAtomic.payload q) (IntegralMixedRoadmapProper.levelIndex q)=[true]
  all_goals simp only [HE,ite_true,ite_false,field]


theorem midpoint_free (q :List Bool) (hv :A q) (HB :FormulaSignSlotRadialProviderProper.Base q)
    (i :Fin (ambient q+1)) (hi :FormulaSignSlotRadialProviderAtomic.depth q ≤ i.val) :
    midpoint q hv i=field q hv (midProducer (D q) (N q) q i.val):=by
  let k:=D q-i.val
  have HD:=ambient_eq q
  have HI:=i.isLt
  have HK:k<captureCount (D q) q:=by
    unfold captureCount levelIndex
    simp only [raw_depth]
    dsimp only [k]
    have HP:=base_depth q HB
    omega
  have HC:=midpoint_capture_eq q hv HB k HK
  have HF:=FormulaSignSlotRadialProviderProper.midpoint_capture_field q hv (base_depth q HB) k HK
  let j:=Fin.cast (congrArg (·+1) (native_ambient_eq q)).symm i
  have HJ:(⟨D q-k,by rw [FormulaSignSlotRadialProviderAtomic.native_dimension];omega⟩ :
      Fin ((B).parameters.ambient (pairFst ((B).key (C q)))+1))=j:=by
    apply Fin.ext
    simp only [j,Fin.val_cast]
    dsimp only [k]
    omega
  rw [HJ] at HF
  have HP:midpoint q hv i=FormulaSignSlotRadialProviderAtomic.geometricPoint (C q)
      (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
      (midFirst (D q) (N q) q+k) j:=by
    unfold midpoint
    exact (congrFun HC j).symm
  simpa only [field,midProducer,k] using HP.trans HF.symm

theorem child_free (q :List Bool) (hv :A q) (i :Fin (ambient q+1))
    (hi :FormulaSignSlotRadialProviderAtomic.depth q ≤ i.val) :
    child q hv i=field q hv (childProducer (D q) (N q) q i.val):=by
  let j:=Fin.cast (congrArg (·+1) (ambient_eq q)) i
  have H:=FormulaSignSlotRadialProviderAtomic.signature_readback q hv
    (Fin.cast (congrArg (·+1) (FormulaSignSlotRadialProviderAtomic.native_dimension q)).symm j)
  have HL:=IntegralMixedChronologicalPointSignatureCode.code_lookup (D q)
    (FormulaSignSlotRadialProviderAtomic.first (D q) (N q) q) (FormulaSignSlotRadialProviderAtomic.frozen q) j
  change Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.signature (D q) (N q) q) j.val)=_ at HL
  simp only [Fin.val_cast] at H
  rw [HL] at H
  have HE:IntegralMixedChronologicalPointSignatureCode.producer (D q)
      (FormulaSignSlotRadialProviderAtomic.first (D q) (N q) q) (FormulaSignSlotRadialProviderAtomic.frozen q) j.val=
      childProducer (D q) (N q) q i.val:=by
    unfold IntegralMixedChronologicalPointSignatureCode.producer
    rw [FormulaSignSlotRadialProviderAtomic.frozen_count,ite_eq_right (by simpa only [j,Fin.val_cast] using Nat.not_lt.mpr hi)]
    unfold childProducer
    have HJ:=j.isLt
    simp only [j,Fin.val_cast,raw_first] at HJ ⊢
    omega
  rw [HE] at H
  simpa only [child,field,j,FormulaSignSlotRadialProviderIdentity.point] using H.symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperLocalFrame
