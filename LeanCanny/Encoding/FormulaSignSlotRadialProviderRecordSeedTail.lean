/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
public import LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
/-! # The actual certified provider executes a literal terminal seed tail -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => certifiedParameters
local notation "D" => certifiedPlan
attribute [local irreducible] parameters spatial source

noncomputable def seedViewPlan := IntegralMixedSourceIntegerRecordAppend.plan P (fun r _=>spatial r)
  positive (fun r _=>spatial_degree r) spatial_cap count source source_nonzero source_degree_cap room

theorem seedViewPlan_eq : seedViewPlan=D := rfl

noncomputable abbrev seedViewData : IntegralMixedFramedHistoryFamilyBits.Data P seedViewPlan := certifiedData

noncomputable def seedInstruction (root : List Bool) : Instruction ((P).ambient root) ((P).width root) :=
  IntegralMixedCanonicalPaddingSeed.instruction (spatial root)
    (IntegralMixedStaticRecordPrefix.cap (spatial root)
      (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap root))

theorem full_seed_tail (root aux : List Bool) (codes : List (List Bool)) (k : ℕ)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((P).ambient root) [] 0 0))) :
    (D).rules root=List.replicate k (seedInstruction root)++
      paddedPast (defaultInstruction P D root) ((D).rules root) (count root+codes.length) := by
  have H := IntegralMixedSourceIntegerSeedTail.full_seed_tail P spatial positive spatial_degree spatial_cap
    count source source_nonzero source_degree_cap room seedViewData root aux codes k ht
  change seedViewPlan.rules root=List.replicate k (seedInstruction root)++
    paddedPast (defaultInstruction P seedViewPlan root) (seedViewPlan.rules root) (count root+codes.length) at H
  rw [seedViewPlan_eq] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
