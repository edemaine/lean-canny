/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLocalFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalOriginalSlice
/-! # The geometric critical-free interval is the actual new word's interval -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
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

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapChain.entry IntegralMixedRoadmapChain.frozen
  IntegralMixedRoadmapProper.labels IntegralMixedRoadmapLocalFrame.field
  IntegralMixedRoadmapProperCritical.originalField

private theorem original_field_eq (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (idx :ℕ):
    IntegralMixedRoadmapProperCritical.originalField hn ht ha hR0 q hv idx=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv idx:=by
  unfold IntegralMixedRoadmapProperCritical.originalField IntegralMixedRoadmapLocalFrame.field
  rfl

private theorem original_reference (q :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd :0<IntegralMixedRoadmapAtomic.depth q)
    (idx :Fin (IntegralMixedRoadmapProperCritical.originalDescriptor hn ht ha hR0 q hv hd).labels.length):
    IntegralMixedRoadmapProperCritical.originalValues hn ht ha hR0 q hv
      ((IntegralMixedRoadmapProperCritical.originalDescriptor hn ht ha hR0 q hv hd).reference idx)=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
        (Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) idx.val)):=by
  let ds:=IntegralMixedRoadmapProperCritical.originalDescriptor hn ht ha hR0 q hv hd
  have HReverse :IntegralMixedRoadmapProperCritical.originalBirth hn ht ha hR0 q-1-(ds.reference idx).val=
      (ds.labels[idx]).val:=by
    have HI:=(ds.labels[idx]).isLt
    simp only [Descriptor.reference,Fin.val_mk]
    omega
  have HLookup :Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) idx.val)=
      (ds.labels[idx]).val:=by
    have HL:=IntegralMixedChronologicalFrameCode.labels_lookup ds idx.val idx.isLt
    have HD:=IntegralMixedChronologicalFrameCode.descriptor_lookup _ _ _
      (IntegralMixedRoadmapProperCritical.original_point_good hn ht ha hR0 q hv hd).1 idx.val
      (by simpa only [ds,IntegralMixedRoadmapProperCritical.originalDescriptor,
        IntegralMixedChronologicalFrameCode.descriptor_length] using idx.isLt)
    exact HD.symm.trans HL
  unfold IntegralMixedRoadmapProperCritical.originalValues
  rw [HReverse,←HLookup]
  exact original_field_eq hn ht ha hR0 q hv _

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c
local notation "h"=>IntegralMixedChronologicalSweepFrame.next d hk
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentValues
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentDescriptor

/-- Critical-freeness of the genuine canonical coarse slice is critical-freeness
of the accepted new word's original source and original chronological fields. -/
theorem WordReceipt.original_critical_free {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hV :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet D old R.leftSpec R.rightSpec side W.word))
    (hOld :∀idx,idx<IntegralMixedFramedPhysicalIndex.arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx)
    (hheight :Disjoint (Ioo (left.value V) (right.value V)) (realCriticalValues Q (line (d).frame h) V h)):
    IntegralMixedRoadmapProperCritical.OriginalSliceCriticalFree hn ht ha hR0
      (packet D old R.leftSpec R.rightSpec side W.word) hV (by rw [depth_packet];omega):=by
  let q:=packet D old R.leftSpec R.rightSpec side W.word
  have hdepth:0<IntegralMixedRoadmapAtomic.depth q:=by dsimp only [q];rw [depth_packet];omega
  let ds:=IntegralMixedRoadmapProperCritical.originalDescriptor hn ht ha hR0 q hV hdepth
  let vs:=IntegralMixedRoadmapProperCritical.originalValues hn ht ha hR0 q hV
  let hs:=IntegralMixedRoadmapProperCritical.originalHeight hn ht ha hR0 q hV hdepth
  have HLabels:IntegralMixedRoadmapProper.labels q=IntegralMixedChronologicalFrameCode.labels d:=
    (coarse_labels_packet hn ht ha hR0 old hv hd left right R side W.word).trans
      (IntegralMixedRoadmapRetainedAppend.parent_labels hn ht ha hR0 old hv hd E he).symm
  have HLen :(d).labels.length=ds.labels.length:=by
    dsimp only [ds,IntegralMixedRoadmapProperCritical.originalDescriptor]
    rw [IntegralMixedChronologicalFrameCode.descriptor_length,HLabels,IntegralMixedChronologicalFrameCode.labels_count]
  have HH :hs.val=ds.labels.length:=by
    change IntegralMixedRoadmapProper.levelIndex q=_
    dsimp only [ds,IntegralMixedRoadmapProperCritical.originalDescriptor]
    rw [IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]
  have HDim :(P).ambient c=n (IntegralMixedRoadmapAtomic.original q)+3:=by
    rw [IntegralMixedRoadmapRetainedAppend.prepared_dimension]
    exact (IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 old).trans
      (congrArg (fun inp=>n inp+3) (original_packet D old R.leftSpec R.rightSpec side W.word).symm)
  have HSource:HEq Q (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q)):=by
    rw [IntegralMixedOriginalRegularSource.spatial_source]
    apply IntegralMixedOriginalRegularSource.source_congr
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      IntegralMixedRoadmapRetainedAppend.preparedRoot,IntegralMixedRoadmapAtomic.root,
      IntegralMixedRoadmapRetainedAppend.candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original,
      q,candidate_packet]
  have HValues :∀idx (hi1 :idx<(d).labels.length) (hi2 :idx<ds.labels.length),
      V ((d).reference ⟨idx,hi1⟩)=vs (ds.reference ⟨idx,hi2⟩):=by
    intro idx hi1 hi2
    have HF:=W.original_frozen_values hn ht ha hR0 old hv hd left right R side hV hOld ⟨idx,hi1⟩
    have HRef:=original_reference hn ht ha hR0 q hV hdepth ⟨idx,hi2⟩
    rw [coarse_labels_packet hn ht ha hR0 old hv hd left right R side W.word] at HRef
    exact HF.symm.trans HRef.symm
  have HSub:=descriptor_critical_subset Q
    (IntegralMixedOriginalRegularSource.source n t R0 (IntegralMixedRoadmapAtomic.original q))
    d ds V vs h hs HDim HSource HLen rfl HH HValues
  have HE:=W.original_endpoint_fields hn ht ha hR0 old hv hd left right R side N hV
  unfold IntegralMixedRoadmapProperCritical.OriginalSliceCriticalFree
  apply Set.disjoint_left.mpr
  intro value hi hc
  have HI :value∈Ioo (left.value V) (right.value V):=by
    change IntegralMixedRoadmapProperCritical.originalField hn ht ha hR0 q hV
        (IntegralMixedRoadmapProper.producer false q)<value ∧
      value<IntegralMixedRoadmapProperCritical.originalField hn ht ha hR0 q hV
        (IntegralMixedRoadmapProper.producer true q) at hi
    rw [original_field_eq hn ht ha hR0 q hV _,original_field_eq hn ht ha hR0 q hV _] at hi
    have HL :IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV
        (IntegralMixedRoadmapProper.producer false q)=left.value V:=HE.1
    have HR :IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hV
        (IntegralMixedRoadmapProper.producer true q)=right.value V:=HE.2
    exact ⟨lt_of_eq_of_lt HL.symm hi.1,lt_of_lt_of_eq hi.2 HR⟩
  exact Set.disjoint_left.mp hheight HI (HSub hc)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
