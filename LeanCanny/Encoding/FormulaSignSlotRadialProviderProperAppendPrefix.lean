/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
/-! # Every general provider endpoint append preserves the complete old prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (dimension initial width depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

noncomputable def preparedRoot (old : List Bool) (l r : List Bool) (side : Bool) :=
  FormulaSignSlotRadialProviderAtomic.root (packet (dimension old) old l r side [])
noncomputable def start (old : List Bool) := IntegralMixedRoadmapChain.rawStart
  (dimension old) (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)

noncomputable def beginBirth (old : List Bool) := endBirth (dimension old) (initial old) old

theorem begin_eq_start (old : List Bool) : beginBirth old=initial old+start old := rfl

theorem prepared_provider (old : List Bool) (l r : List Bool) (side : Bool) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext (preparedRoot old l r side)=
      FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root old) := by
  rw [preparedRoot,FormulaSignSlotRadialProviderAtomic.root_provider,
    FormulaSignSlotRadialProviderAtomic.root_provider,provider_packet]

theorem prepared_count (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    IntegralMixedCausalRecordPlanBits.count (preparedRoot old l r side)=
      IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root old) := by
  unfold IntegralMixedCausalRecordPlanBits.count preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_records,FormulaSignSlotRadialProviderAtomic.root_records,payload_packet]
  exact raw_count old hv hd l r side hE

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters

theorem prepared_dimension (old : List Bool) (l r : List Bool) (side : Bool) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (preparedRoot old l r side)=dimension old :=
  dimension_packet (dimension old) old l r side []

theorem prepared_initial (old : List Bool) (l r : List Bool) (side : Bool) :
    FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old l r side)=initial old :=
  initial_packet (dimension old) old l r side []

theorem prepared_width (old : List Bool) (l r : List Bool) (side : Bool) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.width (preparedRoot old l r side)=width old :=
  width_packet (dimension old) old l r side []

theorem prepared_cap (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (preparedRoot old l r side)=
      FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (FormulaSignSlotRadialProviderAtomic.root old) :=
  FormulaSignSlotRadialProviderRecordPrefix.cap _ _ (prepared_provider old l r side) (prepared_count old hv hd l r side hE)

theorem prepared_source (old : List Bool) (l r : List Bool) (side : Bool) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side))
      (FormulaSignSlotRadialProviderRecordPlan.spatial (FormulaSignSlotRadialProviderAtomic.root old)) :=
  FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ (prepared_provider old l r side)

theorem start_fit (old : List Bool) (hv : A old) :
    start old≤IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root old) := by
  rw [FormulaSignSlotRadialProviderAtomic.root_record_count old hv]
  have HH := IntegralMixedRoadmapChain.rawStart_bound (dimension old)
    (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)
    (by have HD := FormulaSignSlotRadialProviderAtomic.depth_le old
          (FormulaSignSlotRadialProviderAtomic.valid_grammar old hv);omega)
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  exact HH.trans (Nat.le_succ _)

theorem prefix_fit (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r) :
    start old≤IntegralMixedCausalRecordPlanBits.count (preparedRoot old l r side) :=
  (start_fit old hv).trans_eq (prepared_count old hv hd l r side hE).symm

theorem prepared_record (old : List Bool) (hv : A old) (l r : List Bool) (side : Bool) (i : ℕ) (hi : i<start old) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot old l r side) i=
      IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root old) i := by
  unfold preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_record_code,
    FormulaSignSlotRadialProviderAtomic.root_record_code,payload_packet]
  exact prefix_record old hv l r side i hi

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPrefix.snapshot FormulaSignSlotRadialProviderRecordPrefix.observation
  preparedRoot start

theorem prefix_snapshot (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r)
    (j : ℕ) (hj : j≤start old) :
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (preparedRoot old l r side) j
      ((hj.trans (start_fit old hv)).trans_eq (prepared_count old hv hd l r side hE).symm)=
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (FormulaSignSlotRadialProviderAtomic.root old) j
      (hj.trans (start_fit old hv)) := by
  exact FormulaSignSlotRadialProviderRecordPrefix.snapshot_eq _ _ (prepared_provider old l r side)
    (prepared_count old hv hd l r side hE) j _ (fun i hi=>prepared_record old hv l r side i (hi.trans_le hj))

theorem prefix_observation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (l r : List Bool) (side : Bool) (hE : EndpointsGood old l r)
    (j : ℕ) (hj : j≤start old) :
    FormulaSignSlotRadialProviderRecordPrefix.observation (preparedRoot old l r side) j
      ((hj.trans (start_fit old hv)).trans_eq (prepared_count old hv hd l r side hE).symm)=
    FormulaSignSlotRadialProviderRecordPrefix.observation (FormulaSignSlotRadialProviderAtomic.root old) j
      (hj.trans (start_fit old hv)) := by
  exact FormulaSignSlotRadialProviderRecordPrefix.observation_eq _ _ (prepared_provider old l r side)
    (prepared_count old hv hd l r side hE) j _ (fun i hi=>prepared_record old hv l r side i (hi.trans_le hj))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
