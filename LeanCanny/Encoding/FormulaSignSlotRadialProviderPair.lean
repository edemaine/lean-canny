/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderSpatialSource
public import LeanCanny.Encoding.FormulaSignSlotRadialOldProviderRealization
/-! # Paired endpoint providers retain one literal spatial source

Changing the role flag keeps the entire original/label field and external
grid metadata. Hence the actual radius and spatial source remain shared.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def oldOf (ctx : List Bool) := pair (pairFst ctx) (pair [false] (pairSnd (pairSnd ctx)))
theorem oldOf_FP : oldOf∈FP := by polytime [oldOf]
theorem old_role (ctx : List Bool) : ¬FormulaSignSlotRadialExternalContext.external (oldOf ctx) := by
  simp [FormulaSignSlotRadialExternalContext.external,FormulaSignSlotRadialExternalContext.metadata,oldOf]
theorem original_oldOf (ctx : List Bool) :
    FormulaSignSlotRadialExternalContext.original (oldOf ctx)=FormulaSignSlotRadialExternalContext.original ctx := by
  simp only [FormulaSignSlotRadialExternalContext.original,oldOf,pairFst_pair]
theorem candidate_oldOf (ctx : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate (oldOf ctx)=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate ctx := by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,oldOf,pairFst_pair]

theorem radius_oldOf (ctx : List Bool) :
    FormulaSignSlotRadialExternalPrelude.radius (oldOf ctx)=FormulaSignSlotRadialExternalPrelude.radius ctx := by
  simp only [FormulaSignSlotRadialExternalPrelude.radius,FormulaSignSlotRadialExternalPrelude.jointHeader,
    FormulaSignSlotRadialExternalPrelude.joiningCutoff,FormulaSignSlotRadialExternalPrelude.original,
    FormulaSignSlotRadialExternalPrelude.number,FormulaSignSlotRadialExternalContext.gridContext,
    FormulaSignSlotRadialExternalContext.metadata,FormulaSignSlotRadialExternalContext.original,
    FormulaSignSlotRadialExternalContext.number,oldOf,pairFst_pair,pairSnd_pair]

theorem spatial_shared (ctx : List Bool) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial (oldOf ctx))
      (FormulaSignSlotRadialProviderIntegerPlan.spatial ctx) :=
  FormulaSignSlotRadialProviderSpatialSource.spatial_heq _ _ (original_oldOf ctx) (radius_oldOf ctx)

theorem oldOf_packet (H : List Bool) (k : ℕ) (Gamma label : List Bool) (side : Bool) (w : List Bool) :
    oldOf (FormulaSignSlotRadialExternalContext.packet H k Gamma label side w)=
      FormulaSignSlotRadialOldProviderRealization.context (FormulaSignSlotRadialJointLayout.source side H) label
        (pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) (pair [side] w)) := by
  simp only [oldOf,FormulaSignSlotRadialExternalContext.packet,
    FormulaSignSlotRadialOldProviderRealization.context,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderPair
