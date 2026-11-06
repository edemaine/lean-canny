/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendFrozenValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalOriginalSlice
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNoCriticalComplete
/-! # Genuine canonical critical-freeness closes the actual no-critical guard -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem descriptor_critical_subset {a b m l :ℕ} (P1 :SpatialSource a) (P2 :SpatialSource b)
    (d1 :Descriptor a m) (d2 :Descriptor b l) (v1 :Fin m→ℝ) (v2 :Fin l→ℝ)
    (h1 :Fin (a+1)) (h2 :Fin (b+1)) (hab :a=b) (hP :HEq P1 P2)
    (hlen :d1.labels.length=d2.labels.length)
    (hh1 :h1.val=d1.labels.length) (hh2 :h2.val=d2.labels.length)
    (hvalues :∀idx (hi1 :idx<d1.labels.length) (hi2 :idx<d2.labels.length),
      v1 (d1.reference ⟨idx,hi1⟩)=v2 (d2.reference ⟨idx,hi2⟩)):
    realCriticalValues P2 (line d2.frame h2) v2 h2⊆realCriticalValues P1 (line d1.frame h1) v1 h1:=by
  subst b
  cases eq_of_heq hP
  have HE :h1=h2:=Fin.ext (hh1.trans (hlen.trans hh2.symm))
  subst h2
  have HF1 :h1∉d1.frame.frozen:=by rw [d1.frozen_mem,hh1];exact Nat.lt_irrefl _
  have HF2 :h1∉d2.frame.frozen:=by rw [d2.frozen_mem,hh2];exact Nat.lt_irrefl _
  intro value hv
  obtain ⟨p,hp,hheight,hgrad⟩:=(line_realCriticalValues_iff P1 d2.frame v2 h1 HF2 d2.free_normal value).mp hv
  have HP2:=(d2.slice_iff P1 v2 p).mp hp
  have HP1 :p∈slice P1 d1.frame v1:=(d1.slice_iff P1 v1 p).mpr ⟨HP2.1,by
    intro idx
    let other:Fin d2.labels.length:=⟨idx.val,idx.isLt.trans_eq hlen⟩
    have HO:=HP2.2 other
    have HC :(⟨other.val,lt_of_lt_of_le other.isLt d2.length_le⟩:Fin (a+1))=
        ⟨idx.val,lt_of_lt_of_le idx.isLt d1.length_le⟩:=Fin.ext rfl
    rw [HC] at HO
    exact HO.trans (hvalues idx.val idx.isLt other.isLt).symm⟩
  apply (line_realCriticalValues_iff P1 d1.frame v1 h1 HF1 d1.free_normal value).mpr
  refine ⟨p,HP1,hheight,?_⟩
  intro idx hi hih
  apply hgrad idx _ hih
  simpa only [d1.frozen_mem,d2.frozen_mem,hlen] using hi

private theorem original_birth_bound (q : List Bool) :
    FormulaSignSlotRadialProviderProperCritical.originalBirth q≤
      FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) := by
  rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
  simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair]
  unfold FormulaSignSlotRadialProviderProperCritical.originalBirth FormulaSignSlotRadialProviderRecordPlan.fullCount
  rw [←FormulaSignSlotRadialProviderProperCritical.base_count q]
  change FormulaSignSlotRadialProviderAtomic.initial q+_ -1≤FormulaSignSlotRadialProviderAtomic.initial q+_
  omega

private theorem original_field_eq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (i : ℕ)
    (hi : i<FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q)) :
    FormulaSignSlotRadialProviderProperCritical.originalField q hv i=FormulaSignSlotRadialProviderAtomic.field q hv i :=
  FormulaSignSlotRadialProviderFieldEquality.point_env _ _ _ i hi

private theorem original_reference (q :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd :0<FormulaSignSlotRadialProviderAtomic.depth q)
    (idx :Fin (FormulaSignSlotRadialProviderProperCritical.originalDescriptor q hv hd).labels.length):
    FormulaSignSlotRadialProviderProperCritical.originalValues q hv
      ((FormulaSignSlotRadialProviderProperCritical.originalDescriptor q hv hd).reference idx)=
      FormulaSignSlotRadialProviderAtomic.field q hv
        (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) idx.val)):=by
  let ds:=FormulaSignSlotRadialProviderProperCritical.originalDescriptor q hv hd
  have HReverse :FormulaSignSlotRadialProviderProperCritical.originalBirth q-1-(ds.reference idx).val=
      (ds.labels[idx]).val:=by
    have HI:=(ds.labels[idx]).isLt
    simp only [Descriptor.reference,Fin.val_mk]
    omega
  have HLookup :Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) idx.val)=
      (ds.labels[idx]).val:=by
    have HL:=IntegralMixedChronologicalFrameCode.labels_lookup ds idx.val idx.isLt
    have HD:=IntegralMixedChronologicalFrameCode.descriptor_lookup _ _ _
      (FormulaSignSlotRadialProviderProperCritical.original_point_good q hv hd).1 idx.val
      (by simpa only [ds,FormulaSignSlotRadialProviderProperCritical.originalDescriptor,
        IntegralMixedChronologicalFrameCode.descriptor_length] using idx.isLt)
    exact HD.symm.trans HL
  unfold FormulaSignSlotRadialProviderProperCritical.originalValues FormulaSignSlotRadialProviderProperCritical.originalNaturalValues
  rw [HReverse,←HLookup]
  exact original_field_eq q hv _ (by rw [HLookup];exact (ds.labels[idx]).isLt.trans_le (original_birth_bound q))

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  canonicalObservation compiledProgram fullObservation
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd e he
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "q" => packet (dimension old) old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he

local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.source
  FormulaSignSlotRadialProviderProperCritical.originalDescriptor FormulaSignSlotRadialProviderProperCritical.originalBirth
  FormulaSignSlotRadialProviderProperCritical.originalField IntegralMixedRoadmapProper.labels
  IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen

theorem SampledLevel.original_critical_free (S : SampledLevel old hv hd left right R side pMID pChild)
    (hheight : Disjoint (Ioo (left.value V) (right.value V))
      (realCriticalValues (FormulaSignSlotRadialProviderRecordPlan.spatial c) (line (d).frame h) V h)) :
    FormulaSignSlotRadialProviderProperCritical.OriginalSliceCriticalFree
      (q S.receipt.word) S.atomic_valid (by rw [depth_packet];omega) := by
  let node := q S.receipt.word
  have hd' : 0<depth node := by dsimp only [node];rw [depth_packet];omega
  let ds := FormulaSignSlotRadialProviderProperCritical.originalDescriptor node S.atomic_valid hd'
  let vs := FormulaSignSlotRadialProviderProperCritical.originalValues node S.atomic_valid
  let hs := FormulaSignSlotRadialProviderProperCritical.originalHeight node S.atomic_valid hd'
  have HLabels : IntegralMixedRoadmapProper.labels node=IntegralMixedChronologicalFrameCode.labels d :=
    (coarse_labels_packet old hv hd left right R side S.receipt.word).trans
      (FormulaSignSlotRadialProviderRetainedAppend.parent_labels old hv hd e he).symm
  have HLen : (d).labels.length=ds.labels.length := by
    have HC := congrArg WordListRecords.count HLabels
    rw [IntegralMixedRoadmapProper.labels_count,IntegralMixedChronologicalFrameCode.labels_count] at HC
    exact HC.symm.trans (FormulaSignSlotRadialProviderProperCritical.original_labels_length node S.atomic_valid hd').symm
  have HH : hs.val=ds.labels.length := by
    change IntegralMixedRoadmapProper.levelIndex node=_
    exact (FormulaSignSlotRadialProviderProperCritical.original_labels_length node S.atomic_valid hd').symm
  have HDim : (P).ambient c=FormulaSignSlotRadialProviderProperCritical.originalAmbient node :=
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e).trans
      ((dimension_packet _ _ _ _ _ _).symm.trans (FormulaSignSlotRadialProviderAtomic.native_dimension node).symm)
  have HP : FormulaSignSlotRadialProviderRecordPlan.providerContext c=
      FormulaSignSlotRadialProviderRecordPlan.providerContext r :=
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).trans
      (prepared_provider old R.leftSpec R.rightSpec side).symm
  have HRootSource := FormulaSignSlotRadialProviderAtomic.spatial_provider node
  rw [root_packet] at HRootSource
  have HSource : HEq (FormulaSignSlotRadialProviderRecordPlan.spatial c) (FormulaSignSlotRadialProviderAtomic.source node) :=
    (FormulaSignSlotRadialProviderRecordPrefix.source_heq c r HP).trans
      (HRootSource.trans (FormulaSignSlotRadialProviderAtomic.source_provider node S.atomic_valid).symm)
  have HValues : ∀idx (hi1 : idx<(d).labels.length) (hi2 : idx<ds.labels.length),
      V ((d).reference ⟨idx,hi1⟩)=vs (ds.reference ⟨idx,hi2⟩) := by
    intro idx hi1 hi2
    have HF := S.original_frozen_values ⟨idx,hi1⟩
    have HRef := original_reference node S.atomic_valid hd' ⟨idx,hi2⟩
    rw [coarse_labels_packet old hv hd left right R side S.receipt.word] at HRef
    exact HF.symm.trans HRef.symm
  have HSub := descriptor_critical_subset (FormulaSignSlotRadialProviderRecordPlan.spatial c)
    (FormulaSignSlotRadialProviderAtomic.source node) d ds V vs h hs HDim HSource HLen rfl HH HValues
  have HE := S.original_endpoint_fields
  unfold FormulaSignSlotRadialProviderProperCritical.OriginalSliceCriticalFree
  apply Set.disjoint_left.mpr
  intro value hi hc
  have HI : value∈Ioo (left.value V) (right.value V) := by
    change FormulaSignSlotRadialProviderProperCritical.originalField node S.atomic_valid
      (IntegralMixedRoadmapProper.producer false node)<value ∧
      value<FormulaSignSlotRadialProviderProperCritical.originalField node S.atomic_valid
        (IntegralMixedRoadmapProper.producer true node) at hi
    rw [original_field_eq node S.atomic_valid _ S.order_bounds.1,
      original_field_eq node S.atomic_valid _ S.order_bounds.2,HE.1,HE.2] at hi
    exact hi
  exact Set.disjoint_left.mp hheight HI (HSub hc)

theorem SampledLevel.no_critical (S : SampledLevel old hv hd left right R side pMID pChild)
    (hheight : Disjoint (Ioo (left.value V) (right.value V))
      (realCriticalValues (FormulaSignSlotRadialProviderRecordPlan.spatial c) (line (d).frame h) V h)) :
    FormulaSignSlotRadialProviderProperCritical.NoCritical (q S.receipt.word) :=
  FormulaSignSlotRadialProviderProperCritical.noCritical_of_original_critical_free _ S.atomic_valid
    (by rw [depth_packet];omega) (S.original_critical_free hheight)


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
