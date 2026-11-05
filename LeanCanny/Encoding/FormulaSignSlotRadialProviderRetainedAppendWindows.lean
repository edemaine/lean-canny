/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendFrame
/-! # Exact space for both retained child blocks and seed completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters

theorem fresh_last (d : ℕ) (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapChain.freshCount (payload d old e) (depth old)=0 := by
  simp only [FormulaSignSlotRadialProviderAtomic.depth,payload,IntegralMixedRoadmapChain.freshCount,
    IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,IntegralMixedRoadmapChain.append_entry_last,
    IntegralMixedRoadmapChain.levelEntry,WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,IntegralMixedRoadmapEndpointSyntax.fresh,endpoint,
    IntegralMixedRoadmapRetainedAppend.endpoint,IntegralMixedRoadmapEndpointSyntax.field_spec_0,ite_true,Nat.add_zero]

theorem raw_start_last (d : ℕ) (old : List Bool) (e : ℕ) :
    IntegralMixedRoadmapChain.rawStart d (payload d old e) (depth old)=
      IntegralMixedRoadmapChain.rawStart d (FormulaSignSlotRadialProviderAtomic.payload old) (depth old) := by
  unfold payload
  exact IntegralMixedRoadmapChain.append_rawStart_before d (FormulaSignSlotRadialProviderAtomic.payload old)
    (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode d) (depth old) (Nat.le_refl _)

noncomputable def finishBirth (old : List Bool) (e : ℕ) :=
  endBirth (dimension old) (N old) (packet (dimension old) old e [])
noncomputable def fullBirth (old : List Bool) (e : ℕ) :=
  FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e)

theorem finish_eq (old : List Bool) (e : ℕ) :
    finishBirth old e=endBirth (dimension old) (N old) old+2+2*(dimension old-depth old) := by
  unfold finishBirth FormulaSignSlotRadialProviderAtomic.endBirth IntegralMixedRoadmapAtomic.endBirth
  change N old+IntegralMixedRoadmapChain.rawStart (dimension old)
    (FormulaSignSlotRadialProviderAtomic.payload (packet (dimension old) old e []))
    (depth (packet (dimension old) old e []))=
      N old+IntegralMixedRoadmapChain.rawStart (dimension old)
        (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)+2+2*(dimension old-depth old)
  rw [payload_packet,depth_packet,IntegralMixedRoadmapChain.rawStart_succ,raw_start_last,
    IntegralMixedRoadmapChain.blockCount,fresh_last]
  omega

theorem finish_le_full (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) : finishBirth old e≤fullBirth old e := by
  have HC : IntegralMixedCausalRecordPlanBits.count (preparedRoot old e)=
      IntegralMixedRoadmapRecordChain.probedRecordBound (dimension old) := by
    rw [prepared_count old hv hd e he,FormulaSignSlotRadialProviderAtomic.root_record_count old hv]
  have HR := IntegralMixedRoadmapChain.rawStart_bound (dimension old) (payload (dimension old) old e)
    (depth old+1) (by omega)
  unfold finishBirth fullBirth FormulaSignSlotRadialProviderRecordPlan.fullCount
    FormulaSignSlotRadialProviderAtomic.endBirth IntegralMixedRoadmapAtomic.endBirth
  change N old+IntegralMixedRoadmapChain.rawStart (dimension old)
    (FormulaSignSlotRadialProviderAtomic.payload (packet (dimension old) old e []))
    (depth (packet (dimension old) old e []))≤
      FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+
        IntegralMixedCausalRecordPlanBits.count (preparedRoot old e)
  rw [payload_packet,depth_packet,prepared_initial,HC]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem level_room (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentCommands old hv hd e he).length+2+2*(dimension old-depth old)≤(P).cap (preparedRoot old e)+1+1 := by
  have HF := finish_le_full old hv hd e he
  rw [finish_eq] at HF
  rw [parent_length]
  change _≤FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e)+2+1+1
  exact HF.trans (by unfold fullBirth;omega)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
