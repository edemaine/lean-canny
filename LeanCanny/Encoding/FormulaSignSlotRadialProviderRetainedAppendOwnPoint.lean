/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalNatural
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendHeader
/-! # The actual old provider point is eligible for its own retained child -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor

theorem own_endpoint_fit (old : List Bool) :
    FormulaSignSlotRadialProviderAtomic.ownBirth old<endBirth (dimension old) (N old) old := by
  unfold FormulaSignSlotRadialProviderAtomic.ownBirth
  have HI := initial_number old
  have HB := begin_eq old
  omega

local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth

theorem own_point_dimension (old : List Bool) : (RP).ambient (preparedRoot old (E old))=
    (B).parameters.ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context old))) :=
  (prepared_dimension old (E old)).trans (FormulaSignSlotRadialProviderAtomic.native_dimension old).symm

noncomputable def ownPoint (old : List Bool) (hv : A old) :
    Fin ((RP).ambient (preparedRoot old (E old))+1)→ℝ := fun i=>
  FormulaSignSlotRadialProviderAtomic.point old hv
    (Fin.cast (congrArg (·+1) (own_point_dimension old)) i)

private theorem cast_point_heq {n m : ℕ} (h : n=m) (p : Fin (m+1)→ℝ) :
    HEq (fun i : Fin (n+1)=>p (Fin.cast (congrArg (·+1) h) i)) p := by cases h;rfl

theorem ownPoint_heq (old : List Bool) (hv : A old) :
    HEq (ownPoint old hv) (FormulaSignSlotRadialProviderAtomic.point old hv) :=
  cast_point_heq (own_point_dimension old) _

theorem own_source_heq (old : List Bool) (hv : A old) :
    HEq (FormulaSignSlotRadialProviderAtomic.source old) (Q (preparedRoot old (E old))) := by
  have H : HEq (FormulaSignSlotRadialProviderAtomic.source old)
      (Q (FormulaSignSlotRadialProviderAtomic.root old)) := by
    unfold FormulaSignSlotRadialProviderAtomic.source
    rw [FormulaSignSlotRadialProviderAtomic.context_root]
    exact heq_of_eq (FormulaSignSlotRadialProviderAtomic.own_creating_source old hv)
  exact H.trans (FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ (prepared_provider old (E old)).symm)

private theorem occurrence_transport {n m k : ℕ} (V : SpatialSource n) (W : SpatialSource m)
    (h : n=m) (hS : HEq V W) (levels : ℕ→ℝ) (p : Fin (n+1)→ℝ) (q : Fin (m+1)→ℝ)
    (hp : HEq p q) (ho : IntegralMixedAtomicOccurrence.Occurrence V k levels p) :
    IntegralMixedAtomicOccurrence.Occurrence W k levels q := by
  cases h
  cases eq_of_heq hS
  cases eq_of_heq hp
  exact ho

theorem own_occurrence (old : List Bool) (hv : A old) :
    IntegralMixedAtomicOccurrence.Occurrence (Q (preparedRoot old (E old))) (depth old)
      (FormulaSignSlotRadialProviderAtomic.levels old hv) (ownPoint old hv) :=
  occurrence_transport _ _ (own_point_dimension old).symm (own_source_heq old hv) _ _ _
    (ownPoint_heq old hv).symm (FormulaSignSlotRadialProviderAtomic.occurrence old hv)

private theorem reverse_reverse (b i : ℕ) (hi : i<b) : b-1-(b-1-i)=i := by omega

private theorem reference_reverse {n b : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n b)
    (i : Fin d.labels.length) : b-1-(d.reference i).val=(d.labels.get i).val := by
  change b-1-(b-1-(d.labels.get i).val)=(d.labels.get i).val
  exact reverse_reverse b _ (d.labels.get i).isLt

theorem parent_frozen_value (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (i : Fin (parentDescriptor old hv hd e he).labels.length) :
    parentValues old hv hd e he ((parentDescriptor old hv hd e he).reference i)=
      FormulaSignSlotRadialProviderAtomic.levels old hv i.val := by
  let d := parentDescriptor old hv hd e he
  have HL := IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
  rw [parent_labels old hv hd e he] at HL
  have HE : (parentCommands old hv hd e he).length-1-(d.reference i).val=
      Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen old) i.val) :=
    (reference_reverse d i).trans HL.symm
  rw [parent_values,HE]
  rfl

theorem parent_endpoint_value (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    parentValues old hv hd e he (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he))=
      FormulaSignSlotRadialProviderAtomic.field old hv e := by
  rw [parent_values]
  apply congrArg (FormulaSignSlotRadialProviderAtomic.field old hv)
  change (parentCommands old hv hd e he).length-1-((parentCommands old hv hd e he).length-1-e)=e
  exact reverse_reverse _ e (he.trans_eq (parent_length old hv hd e he).symm)

theorem own_height_field (old : List Bool) (hv : A old) :
    FormulaSignSlotRadialProviderAtomic.field old hv (E old)=FormulaSignSlotRadialProviderAtomic.point old hv
      ⟨depth old,by rw [FormulaSignSlotRadialProviderAtomic.native_dimension]
                    exact Nat.lt_succ_of_le (FormulaSignSlotRadialProviderAtomic.depth_le old
                      (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv))⟩ := by
  have HA := FormulaSignSlotRadialProviderAtomic.own_active old hv
  have HZ := FormulaSignSlotRadialProviderRecordPrefix.scalarValue_of_valid old hv (E old)
    (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ HA).1
  have HZ' : IntegralFramedPhysicalCompanionPoint.scalarValue B T FormulaSignSlotRadialProviderAtomic.bank_represents
      (FormulaSignSlotRadialProviderAtomic.context old) (FormulaSignSlotRadialProviderAtomic.word old) (E old)=
      InfinitesimalSign.encode 0 := HZ
  have H := (FormulaSignSlotRadialProviderAtomic.scalarValue_zero_iff_field _ _
    (FormulaSignSlotRadialProviderAtomic.full_valid old hv) _ HA).mp HZ'
  rw [FormulaSignSlotRadialProviderAtomic.own_height_point old hv] at H
  have HS := IntegralFramedPhysicalCompanionPoint.selected_of_frame B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (FormulaSignSlotRadialProviderAtomic.context old) (E old) (FormulaSignSlotRadialProviderAtomic.frozen old)
    (depth old) (depth old) (FormulaSignSlotRadialProviderAtomic.native_point_good old hv)
    (FormulaSignSlotRadialProviderAtomic.native_creating_command old hv)
  exact H.trans (congrArg (FormulaSignSlotRadialProviderAtomic.point old hv) (Fin.ext HS))

attribute [local irreducible] ownPoint FormulaSignSlotRadialProviderAtomic.levels

theorem own_point_eligible (old : List Bool) (hv : A old) (hd : depth old<dimension old) :
    let e := E old
    let he := own_endpoint_fit old
    let d := parentDescriptor old hv hd e he
    let hk := parent_descriptor_fit old hv hd e he
    ownPoint old hv∈slice (Q (preparedRoot old e)) d.frame (parentValues old hv hd e he) ∧
      ownPoint old hv (IntegralMixedChronologicalSweepFrame.next d hk)=
        parentValues old hv hd e he (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)) ∧
      ∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→
        i≠childCoordinate old hv hd e he→(MvPolynomial.pderiv i
          (FermatCriticalHomogenization.polynomial (Q (preparedRoot old e)).low
            (Q (preparedRoot old e)).leading (Q (preparedRoot old e)).degree)).eval₂
              (Int.castRingHom ℝ) (ownPoint old hv)=0 := by
  dsimp only
  let e := E old
  let he := own_endpoint_fit old
  let d := parentDescriptor old hv hd e he
  let hk := parent_descriptor_fit old hv hd e he
  have HO := own_occurrence old hv
  have HL := parent_descriptor_length old hv hd e he
  refine ⟨?_,?_,?_⟩
  · apply (d.slice_iff (Q (preparedRoot old e)) (parentValues old hv hd e he) (ownPoint old hv)).mpr
    refine ⟨HO.zero,?_⟩
    intro i
    have HI : i.val<depth old := i.isLt.trans_eq HL
    exact (HO.frozen ⟨i.val,i.isLt.trans_le d.length_le⟩ HI).trans
      (parent_frozen_value old hv hd e he i).symm
  · rw [parent_endpoint_value,own_height_field]
    unfold ownPoint
    apply congrArg (FormulaSignSlotRadialProviderAtomic.point old hv)
    apply Fin.ext
    simpa only [Fin.val_cast,IntegralMixedChronologicalSweepFrame.next] using HL
  · intro i hi _
    have HNot : ¬(i=IntegralMixedChronologicalSweepFrame.next d hk ∨i∈d.frame.frozen) := by
      simpa only [Finset.mem_insert] using hi
    have HS := not_or.mp HNot
    have HI : ¬i.val<d.labels.length := fun h=>HS.2 ((d.frozen_mem i).mpr h)
    have HNe : i.val≠d.labels.length := by
      intro h
      exact HS.1 (Fin.ext h)
    have HDepth : d.labels.length=depth old := HL
    exact HO.critical i (by omega) (by omega)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
