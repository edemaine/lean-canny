/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointMembership
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperProbeWitness
/-! # Accepted midpoint coordinates are genuine bounded ordinary roots -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem root_rank_lt_card (s : Finset ℝ) (v : ℝ) (hv : v∈s) :
    OrderedRealRootWindow.rank s v<s.card :=by
  obtain ⟨i,rfl⟩:=OrderedRealCells.exists_root s v hv
  change (s.filter (fun y=>y<OrderedRealCells.root s i)).card<s.card
  exact (OrderedRealCells.root_rank s i).symm.trans_lt i.isLt
private theorem family_coordinate_member (F : IntegralMixedCutSource.Family) (key : List Bool)
    (φ : (F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (p : Fin (F.ambient key+1)→ℝ)
    (hp : p∈IntegralMixedSelectedPhysicalFiber.physical (F.state key) (F.birth_bound key) (F.rule key) φ t)
    (j : Fin (F.ambient key-(F.rule key).critical.offset.val+1)) :
    p (ClearedCoordinateCritical.freeIndex (F.rule key).critical.offset.val (fit (F.rule key)).le j)∈
      IntegralMixedFrozenFrameSectionCode.roots (F.state key) (F.birth_bound key) (F.rule key) φ t j :=
  IntegralMixedFrozenFrameSectionCode.coordinate_mem (F.state key) (F.birth_bound key) (F.rule key) φ t ⟨p,hp⟩ j
private theorem family_coordinate_value_member (F : IntegralMixedCutSource.Family) (key : List Bool)
    (φ : (F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (p : Fin (F.ambient key+1)→ℝ)
    (hp : p∈IntegralMixedSelectedPhysicalFiber.physical (F.state key) (F.birth_bound key) (F.rule key) φ t)
    (j : Fin (F.ambient key-(F.rule key).critical.offset.val+1)) (v : ℝ)
    (hv : p (ClearedCoordinateCritical.freeIndex (F.rule key).critical.offset.val (fit (F.rule key)).le j)=v) :
    v∈IntegralMixedFrozenFrameSectionCode.roots (F.state key) (F.birth_bound key) (F.rule key) φ t j :=by
  have HM:=family_coordinate_member F key φ t p hp j
  exact hv ▸ HM
private theorem family_root_rank_bound (F : IntegralMixedCutSource.Family) (key : List Bool)
    (φ : (F.state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (t : ℝ)
    (j : Fin (F.ambient key-(F.rule key).critical.offset.val+1)) (v : ℝ)
    (hv : v∈IntegralMixedFrozenFrameSectionCode.roots (F.state key) (F.birth_bound key) (F.rule key) φ t j) :
    IntegralMixedSelectedRootRank.rank (F.state key) (F.birth_bound key) (F.rule key) φ t j v<2^F.width key :=
  (root_rank_lt_card _ _ hv).trans_le
    (IntegralMixedFrozenFrameSectionCode.roots_card (F.state key) (F.birth_bound key) (F.rule key) φ t j)
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D"=>FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H"=>FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedCriticalSweep.selected IntegralMixedFrozenFrameSectionCode.roots

theorem midpoint_coordinate_mem (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀j,φ (((G).state (parentKey false z)).bank.numerator j)/
      (((G).state (parentKey false z)).bank.denominator j:ℝ)=
      originalValue (atomic z) hv ((G).birth (parentKey false z)-1-j.val)) :
    originalValue (atomic z) hv (pointProducer true z)∈IntegralMixedFrozenFrameSectionCode.roots
      ((G).state (parentKey false z)) ((G).birth_bound _) ((G).rule (parentKey false z)) φ
      ((originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2)
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey false z)
        (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13 (parent false z))) :=by
  let old:=parentKey false z
  let r:=(G).rule old
  let j:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old
    (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13 (parent false z))
  let i:=dimension z-coordinate z
  have HCoord : coordinate z≤dimension z:=by have HH:=hr.1.2.2.2.2;omega
  have HLo : offset z≤coordinate z:=by rw [offset_count];exact hr.1.2.2.2.1
  have HI : i<IntegralMixedRoadmapProper.captureCount (dimension z) (atomic z):=by
    have HH : IntegralMixedRoadmapProper.levelIndex (atomic z)+1≤coordinate z:=HLo
    dsimp only [i]
    unfold IntegralMixedRoadmapProper.captureCount
    omega
  have HPhysical:=midpoint_capture_physical z hv hd hr i HI φ hφ
  let ix:=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j
  have HO:=rule_offset false z hv hr
  have HJ:=selected_coordinate false z hv hr
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at HO HJ
  have HIndex : ix.val=coordinate z:=by
    change r.critical.offset.val+j.val=coordinate z
    exact (congrArg₂ Nat.add HO HJ).trans (by
      unfold relativeCoordinate
      exact Nat.add_sub_of_le HLo)
  have HMinus : dimension z-i=coordinate z:=by dsimp only [i];omega
  have HF:=FormulaSignSlotRadialProviderProper.midpoint_capture_field (atomic z) hv hd i HI
  let b:=IntegralMixedRoadmapProper.midFirst (dimension z) (initial z) (atomic z)+i
  have HLabel : pointProducer true z=b:=by
    simp only [pointProducer,ite_true,IntegralMixedRoadmapProper.midProducer,b,i]
  have HNative := FormulaSignSlotRadialProviderAtomic.native_dimension (atomic z)
  have HPIndex : Fin.cast (congrArg (·+1) (midpoint_row_ambient z)).symm ix=
      (⟨dimension z-i,by
        exact (Nat.lt_succ_of_le (Nat.sub_le _ _)).trans_eq (congrArg (fun n : ℕ=>n+1) HNative.symm)⟩ :
        Fin ((P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context (atomic z))))+1)) :=by
    apply Fin.ext
    exact HIndex.trans HMinus.symm
  have HPValue : midpointRowCapture z hv i ix=
      FormulaSignSlotRadialProviderAtomic.field (atomic z) hv b :=by
    unfold midpointRowCapture
    exact (congrArg (FormulaSignSlotRadialProviderAtomic.geometricPoint
      (FormulaSignSlotRadialProviderAtomic.context (atomic z)) (FormulaSignSlotRadialProviderAtomic.word (atomic z))
      (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) b) HPIndex).trans HF.symm
  have HA:=FormulaSignSlotRadialProviderProper.midpoint_capture_active (atomic z) hv hd i HI
  have HB : b<FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=by
    have HH:=IntegralFramedPhysicalCompanionPoint.active_direct B FormulaSignSlotRadialProviderRecordPlan.tables
      (FormulaSignSlotRadialProviderAtomic.context (atomic z)) b HA
    have HB0 : b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters
        ((B).key (FormulaSignSlotRadialProviderAtomic.context (atomic z))):=HH.1
    exact HB0.trans_eq (FormulaSignSlotRadialProviderAtomic.native_full_prefix (atomic z))
  have HV : midpointRowCapture z hv i ix=originalValue (atomic z) hv (pointProducer true z):=
    HPValue.trans ((originalValue_field (atomic z) hv b HB).symm.trans
      (congrArg (originalValue (atomic z) hv) HLabel.symm))
  exact family_coordinate_value_member G old φ
    ((originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2)
    (midpointRowCapture z hv i) HPhysical j (originalValue (atomic z) hv (pointProducer true z)) HV


theorem midpoint_rank_bounded (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth (atomic z))
    (hr : FormulaSignSlotRadialProviderProperRowWitness.RowGood z)
    (φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀j,φ (((G).state (parentKey false z)).bank.numerator j)/
      (((G).state (parentKey false z)).bank.denominator j:ℝ)=
      originalValue (atomic z) hv ((G).birth (parentKey false z)-1-j.val)) :
    IntegralMixedSelectedRootRank.rank ((G).state (parentKey false z)) ((G).birth_bound _)
      ((G).rule (parentKey false z)) φ
      ((originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2)
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey false z)
        (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13 (parent false z)))
      (originalValue (atomic z) hv (pointProducer true z))<2^FormulaSignSlotRadialProviderAtomic.width (atomic z) :=by
  have HM:=midpoint_coordinate_mem z hv hd hr φ hφ
  let old:=parentKey false z
  let j:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G old
    (IntegralCriticalHistoryTask.get P IntegralCriticalHistoryTask.Field.slot13 (parent false z))
  let t:=(originalValue (atomic z) hv (oldProducer false z)+originalValue (atomic z) hv (oldProducer true z))/2
  let roots:=IntegralMixedFrozenFrameSectionCode.roots ((G).state old) ((G).birth_bound old) ((G).rule old) φ t j
  have HB:=family_root_rank_bound G old φ t j (originalValue (atomic z) hv (pointProducer true z)) HM
  have HW:=probe_parent_width false z
  simp only [FormulaSignSlotRadialProviderRecordPlan.bank] at HW
  with_unfolding_all
    exact HB.trans_eq (congrArg (fun b : ℕ=>2^b) HW)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
