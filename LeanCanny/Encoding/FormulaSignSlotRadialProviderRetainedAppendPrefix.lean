/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
/-! # The actual equal extension preserves every old prefix observation -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (dimension initial width depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

noncomputable def preparedRoot (old : List Bool) (e : ℕ) :=
  FormulaSignSlotRadialProviderAtomic.root (packet (dimension old) old e [])
noncomputable def start (old : List Bool) := IntegralMixedRoadmapChain.rawStart
  (dimension old) (FormulaSignSlotRadialProviderAtomic.payload old) (depth old)

theorem prepared_provider (old : List Bool) (e : ℕ) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext (preparedRoot old e)=
      FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root old) := by
  rw [preparedRoot,FormulaSignSlotRadialProviderAtomic.root_provider,
    FormulaSignSlotRadialProviderAtomic.root_provider,provider_packet]

theorem prepared_count (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    IntegralMixedCausalRecordPlanBits.count (preparedRoot old e)=
      IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root old) := by
  unfold IntegralMixedCausalRecordPlanBits.count preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_records,FormulaSignSlotRadialProviderAtomic.root_records,payload_packet]
  exact raw_count old hv hd e he

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters

theorem prepared_dimension (old : List Bool) (e : ℕ) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (preparedRoot old e)=dimension old :=
  dimension_packet (dimension old) old e []

theorem prepared_initial (old : List Bool) (e : ℕ) :
    FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)=initial old :=
  initial_packet (dimension old) old e []

theorem prepared_width (old : List Bool) (e : ℕ) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.width (preparedRoot old e)=width old :=
  width_packet (dimension old) old e []

theorem prepared_cap (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (preparedRoot old e)=
      FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (FormulaSignSlotRadialProviderAtomic.root old) :=
  FormulaSignSlotRadialProviderRecordPrefix.cap _ _ (prepared_provider old e) (prepared_count old hv hd e he)

theorem prepared_source (old : List Bool) (e : ℕ) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e))
      (FormulaSignSlotRadialProviderRecordPlan.spatial (FormulaSignSlotRadialProviderAtomic.root old)) :=
  FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ (prepared_provider old e)

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
    (e : ℕ) (he : e<endBirth (dimension old) (initial old) old) :
    start old≤IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) :=
  (start_fit old hv).trans_eq (prepared_count old hv hd e he).symm

theorem prepared_record (old : List Bool) (hv : A old) (e i : ℕ) (hi : i<start old) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) i=
      IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root old) i := by
  unfold preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_record_code,
    FormulaSignSlotRadialProviderAtomic.root_record_code,payload_packet]
  exact prefix_record old hv e i hi

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPrefix.snapshot FormulaSignSlotRadialProviderRecordPrefix.observation
  preparedRoot start

theorem prefix_snapshot (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (initial old) old)
    (j : ℕ) (hj : j≤start old) :
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (preparedRoot old e) j
      ((hj.trans (start_fit old hv)).trans_eq (prepared_count old hv hd e he).symm)=
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (FormulaSignSlotRadialProviderAtomic.root old) j
      (hj.trans (start_fit old hv)) := by
  exact FormulaSignSlotRadialProviderRecordPrefix.snapshot_eq _ _ (prepared_provider old e)
    (prepared_count old hv hd e he) j _ (fun i hi=>prepared_record old hv e i (hi.trans_le hj))

theorem prefix_observation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (initial old) old)
    (j : ℕ) (hj : j≤start old) :
    FormulaSignSlotRadialProviderRecordPrefix.observation (preparedRoot old e) j
      ((hj.trans (start_fit old hv)).trans_eq (prepared_count old hv hd e he).symm)=
    FormulaSignSlotRadialProviderRecordPrefix.observation (FormulaSignSlotRadialProviderAtomic.root old) j
      (hj.trans (start_fit old hv)) := by
  exact FormulaSignSlotRadialProviderRecordPrefix.observation_eq _ _ (prepared_provider old e)
    (prepared_count old hv hd e he) j _ (fun i hi=>prepared_record old hv e i (hi.trans_le hj))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
