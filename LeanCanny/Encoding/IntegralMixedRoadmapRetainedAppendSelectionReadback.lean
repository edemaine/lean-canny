/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendFieldMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChild
/-! # Chronological selected coordinates agree with both typed companion lists -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<beginBirth hn ht ha hR0 old)
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "d"=>parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "q"=>packet (D old) old e []
local notation "sel"=>IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context parentCommands parentDescriptor

theorem midpoint_selection_selected (i :Fin (js).length) :
    sel ((older).length+(js).length-1-i.val)=((js).get i).val.val:=by
  let fs:=IntegralMixedChronologicalMidpointSignature.orderedFree d hk a a
  have HF :fs.length=D old-IntegralMixedRoadmapAtomic.depth old:=by
    rw [IntegralMixedChronologicalMidpointSignature.orderedFree_length,
      IntegralMixedChronologicalMidpointSignature.freeCount,parent_descriptor_length,prepared_dimension]
    omega
  have HL:=midpoint_selection_count hn ht ha hR0 old hv hd e he
  have HP:=parent_length hn ht ha hR0 old hv hd e he
  have HMB:=midpoint_birth hn ht ha hR0 old e
  have HMC:=midpoint_count hn ht ha hR0 old e
  dsimp only at HL HP HMB HMC
  by_cases hLast :i.val=fs.length
  · have HB :(older).length+(js).length-1-i.val=IntegralMixedRoadmapProper.midBirth (D old) (N old) q:=by
      change _=beginBirth hn ht ha hR0 old at HP
      omega
    rw [HB,midpoint_anchor_selected hn ht ha hR0 old hv hd e he []]
    have HG :((js).get i).val.val=IntegralMixedRoadmapAtomic.depth old+1:=by
      change ((fs++[midpointObjective hn ht ha hR0 old hv hd e he]).get i).val.val=_
      rw [List.get_eq_getElem,List.getElem_append_right (by omega :fs.length≤ i.val)]
      simp only [hLast,Nat.sub_self,List.getElem_singleton,midpointObjective,parent_descriptor_length]
    rw [HG,IntegralMixedRoadmapProper.levelIndex,depth_packet]
    omega
  · have HI :i.val<fs.length:=by have H:=i.isLt;omega
    have HG :((js).get i).val.val=IntegralMixedRoadmapAtomic.depth old+1+i.val:=by
      change ((fs++[midpointObjective hn ht ha hR0 old hv hd e he]).get i).val.val=_
      simp only [List.get_eq_getElem,List.getElem_append_left HI]
      exact (IntegralMixedChronologicalMidpointSignature.orderedFree_get d hk a a ⟨i.val,HI⟩).trans
        (by rw [parent_descriptor_length])
    let j:=fs.length-1-i.val
    have HJ :j<IntegralMixedRoadmapProper.captureCount (D old) q:=by dsimp only [j];omega
    have HB :(older).length+(js).length-1-i.val=
        IntegralMixedRoadmapProper.midFirst (D old) (N old) q+j:=by
      change _=beginBirth hn ht ha hR0 old at HP
      unfold IntegralMixedRoadmapProper.midFirst
      dsimp only [j]
      omega
    rw [HB,midpoint_capture_selected hn ht ha hR0 old hv hd e he [] j HJ,HG]
    dsimp only [j]
    omega

theorem child_selection_selected (i :Fin (cs).length) :
    sel ((older).length+(js).length+(cs).length-1-i.val)=((cs).get i).val.val:=by
  let dc:=childDescriptor hn ht ha hR0 old hv hd e he
  let fs:=dc.orderedFree
  have HDC :dc.labels.length=IntegralMixedRoadmapAtomic.depth old+1:=by
    simp only [dc,childDescriptor,retainMany_length,Descriptor.freeze_length,parent_descriptor_length]
  have HF :fs.length=D old-IntegralMixedRoadmapAtomic.depth old:=by
    rw [Descriptor.orderedFree_length,Descriptor.freeCount,HDC,prepared_dimension]
    omega
  have HL:=child_selection_count hn ht ha hR0 old hv hd e he
  have HM:=midpoint_selection_count hn ht ha hR0 old hv hd e he
  have HP:=parent_length hn ht ha hR0 old hv hd e he
  have HCA:=child_anchor hn ht ha hR0 old e
  have HCC:=child_count hn ht ha hR0 old e
  dsimp only at HL HM HP HCA HCC
  by_cases hLast :i.val=fs.length
  · have HB :(older).length+(js).length+(cs).length-1-i.val=
        IntegralMixedRoadmapAtomic.anchor (D old) (N old) q:=by
      change _=beginBirth hn ht ha hR0 old at HP
      omega
    rw [HB,child_anchor_selected hn ht ha hR0 old hv hd e he]
    have HG :((cs).get i).val.val=IntegralMixedRoadmapAtomic.depth old+1:=by
      change ((fs++[childObjective hn ht ha hR0 old hv hd e he]).get i).val.val=_
      rw [List.get_eq_getElem,List.getElem_append_right (by omega :fs.length≤ i.val)]
      simp only [hLast,Nat.sub_self,List.getElem_singleton,childObjective,midpointObjective,parent_descriptor_length]
    rw [HG,depth_packet]
  · have HI :i.val<fs.length:=by have H:=i.isLt;omega
    have HG :((cs).get i).val.val=IntegralMixedRoadmapAtomic.depth old+1+i.val:=by
      change ((fs++[childObjective hn ht ha hR0 old hv hd e he]).get i).val.val=_
      simp only [List.get_eq_getElem,List.getElem_append_left HI]
      exact (Descriptor.orderedFree_get dc ⟨i.val,HI⟩).trans (by rw [HDC])
    let j:=fs.length-1-i.val
    have HJ :j<IntegralMixedRoadmapAtomic.free (D old) q:=by dsimp only [j];omega
    have HB :(older).length+(js).length+(cs).length-1-i.val=
        IntegralMixedRoadmapAtomic.first (D old) (N old) q+j:=by
      change _=beginBirth hn ht ha hR0 old at HP
      unfold IntegralMixedRoadmapAtomic.first
      dsimp only [j]
      omega
    rw [HB,child_capture_selected hn ht ha hR0 old hv hd e he j HJ,HG]
    dsimp only [j]
    omega

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
